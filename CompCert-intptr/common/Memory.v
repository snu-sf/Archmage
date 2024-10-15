(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*          with contributions from Andrew Appel, Rob Dockins,         *)
(*          and Gordon Stewart (Princeton University)                  *)
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

(** This file develops the memory model that is used in the dynamic
  semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Zwf.
Require Import Axioms.
Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Export Memdata.
Require Export Memtype.
Require Export sflib.
Require Import Classical.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Module Mem <: MEM.

Definition perm_order' (po: option permission) (p: permission) :=
  match po with
  | Some p' => perm_order p' p
  | None => False
 end.

Definition perm_order'' (po1 po2: option permission) :=
  match po1, po2 with
  | Some p1, Some p2 => perm_order p1 p2
  | _, None => True
  | None, Some _ => False
 end.

Inductive in_range (z: Z) (r: Z * Z) :=
| in_range_intro
    (FST: (fst r) <= z)
    (SND: (snd r) > z) :
  in_range z r.

Definition in_rangeb (z:Z) (r: Z * Z) : bool :=
  if (Z.leb (fst r) z) && (Z.ltb z (snd r)) then true else false.

Lemma in_range_iff: forall z r,
    in_range z r <-> in_rangeb z r = true.
Proof.
  split; i.
  - inv H. des. unfold in_rangeb. des_ifs. lia.
  - unfold in_rangeb in H. des_ifs. econs; lia.
Qed.

(* Meaning of (addr_in_block mem_concrete mem_access addr blk) :  *)
(* a concrete address "addr" corresponds to a logical address in the logical block "blk". *)
Inductive addr_in_block (conc:PTree.t Z) (acc:PMap.t (Z -> perm_kind -> option permission)) (addr:Z) (blk: block) : Prop :=
| addr_in_block_intro
    caddr
    (CONCRETE: conc!blk = Some caddr)
    (PERM: exists perm, acc#blk (addr-caddr) Max = Some perm)
    (POS: 0 <= (addr-caddr) < Ptrofs.modulus) :
    addr_in_block conc acc addr blk.

Definition addr_is_in_block (conc:PTree.t Z) (acc:PMap.t (Z -> perm_kind -> option permission)) (addr:Z) (blk: block) : bool :=
  match (conc!blk) with
  | Some caddr => match acc#blk (addr-caddr) Max with
                 | Some _ => Z.leb 0 (addr-caddr) && Z.ltb (addr-caddr) Ptrofs.modulus
                 | _ => false
                 end
  | _ => false
  end.

Lemma addr_in_block_iff: forall conc acc addr blk,
    addr_in_block conc acc addr blk <-> addr_is_in_block conc acc addr blk = true.
Proof.
  split; i.
  - inv H. des. unfold addr_is_in_block. des_ifs. lia.
  - unfold addr_is_in_block in H. des_ifs. econs; eauto. lia.
Qed.

(* weak valid pointer & max permission *)

Definition _valid_pointer (acc:PMap.t (Z -> perm_kind -> option permission)) (blk: block) (ofs: Z) (k: perm_kind) : Prop :=
  perm_order' (acc#blk ofs k) Nonempty.

Definition _weak_valid_pointer (acc:PMap.t (Z -> perm_kind -> option permission)) (blk: block) (ofs: Z) (k: perm_kind) : Prop :=
  _valid_pointer acc blk ofs k \/ _valid_pointer acc blk (ofs - 1) k.

Record mem' : Type := mkmem {
  mem_contents: PMap.t (ZMap.t memval);  (**r [block -> offset -> memval] *)
  mem_access: PMap.t (Z -> perm_kind -> option permission);
                                         (**r [block -> offset -> kind -> option permission] *)
  mem_concrete: PTree.t Z; (** [block -> option Z] **)
  nextblock: block;
  access_max:
    forall b ofs, perm_order'' (mem_access#b ofs Max) (mem_access#b ofs Cur);
  nextblock_noaccess:
    forall b ofs k, ~(Plt b nextblock) -> mem_access#b ofs k = None;
  contents_default:
    forall b, fst mem_contents#b = Undef;
  nextblocks_logical:
    forall b, ~(Plt b nextblock) -> mem_concrete!b = None;
  valid_address_bounded:
    forall bo addr (IN_BLOCK: addr_in_block mem_concrete mem_access addr bo),
      addr < Ptrofs.modulus - 1;
  no_concrete_overlap:
    forall addr, uniqueness (addr_in_block mem_concrete mem_access addr);
  concrete_align:
    forall b zero_addr (CADDR: mem_concrete!b = Some zero_addr)
      ofs chunk (RPERM: forall o, ofs <= o < ofs + (size_chunk chunk) -> perm_order' (mem_access#b o Max) Nonempty),
      (align_chunk chunk | zero_addr);
  weak_valid_address_range:
    forall b zero_addr ofs (CADDR: mem_concrete!b = Some zero_addr)
                      (RANGE: 0 <= ofs < Ptrofs.modulus)
                      (WVLD: _weak_valid_pointer mem_access b ofs Max),
      in_range (zero_addr + ofs) (1, Ptrofs.modulus);
}.
Definition mem := mem'.

Lemma mkmem_ext:
  forall cont1 cont2 acc1 acc2 conc1 conc2 nxt1 nxt2 a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g1 g2 h1 h2,
  cont1=cont2 -> acc1=acc2 -> conc1=conc2 -> nxt1=nxt2 ->
  mkmem cont1 acc1 conc1 nxt1 a1 b1 c1 d1 e1 f1 g1 h1 = mkmem cont2 acc2 conc2 nxt2 a2 b2 c2 d2 e2 f2 g2 h2.
Proof.
  intros. subst. f_equal; apply proof_irr.
Qed.

Lemma _weak_valid_block_zero m b addr
    (IN_BLOCK: addr_in_block m.(mem_concrete) m.(mem_access) addr b) :
  <<INRANGE: 1 <= addr>>.
Proof.
  specialize (weak_valid_address_range m). intros WVLD. inv IN_BLOCK.
  des. exploit WVLD; eauto.
  { left. unfold _valid_pointer. rewrite PERM. ss. eapply perm_any_N. }
  i. inv H. ss. r. lia.
Qed.

(* Lemma valid_addr_bound_cant_implies_weak_valid_bound *)
(*   m b zero_addr ofs *)
(*   (CADDR: m.(mem_concrete)!b = Some zero_addr) *)
(*   (RANGE: 0 <= ofs < Ptrofs.modulus) *)
(*   (WVLD: _weak_valid_pointer m.(mem_access) b ofs Max) : *)
(*   zero_addr + ofs < Ptrofs.modulus. *)
(* Proof. *)
(*   specialize (valid_address_bounded m). i. *)
(*   destruct WVLD as [VLD | WVLD]. *)
(*   - assert (addr_in_block (mem_concrete m) (mem_access m) (zero_addr + ofs) b). *)
(*     { econs; eauto; [|lia]. *)
(*       unfold _valid_pointer, perm_order' in *. des_ifs. *)
(*       replace (zero_addr + ofs - zero_addr) with ofs by lia. eauto. } *)
(*     eapply H in H0. lia. *)
(*   - assert (addr_in_block (mem_concrete m) (mem_access m) (zero_addr + (ofs - 1)) b). *)
(*     { econs; eauto. *)
(*       (* split;[|lia]. replace (zero_addr + (ofs - 1) - zero_addr) with (ofs - 1) by lia. *) *)
(*       (* it can't guarantee zero size weak valid pointer's upperbound *) *)
(*       (* (if permission in ofs = -1, (b, ofs + 1) ~ paddr -> paddr < Ptorfs.modulus is not guaranteed  *) *)
(* Abort. *)

Lemma _valid_pointer_range
  m b addr
  (IN_BLOCK: addr_in_block m.(mem_concrete) m.(mem_access) addr b) :
  <<INRANGE: in_range addr (1, Ptrofs.modulus - 1)>>.
Proof.
  specialize (weak_valid_address_range m). intros WVLD.
  exploit valid_address_bounded; eauto. intros BOUND. inv IN_BLOCK.
  des. exploit WVLD; eauto.
  { unfold _weak_valid_pointer, _valid_pointer. rewrite PERM.
    left. ss. eapply perm_any_N. }
  replace (caddr + (addr - caddr)) with addr by lia. ii. inv H.
  econs; eauto. unfold snd. simpl in FST, SND.
  destruct (zeq addr (Ptrofs.modulus - 1)); [lia|lia].
Qed.

(** * Validity of blocks and accesses *)

(** A block address is valid if it was previously allocated. It remains valid
  even after being freed. *)

Definition valid_block (m: mem) (b: block) := Plt b (nextblock m).

Theorem valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.
Proof.
  intros; red; intros. subst b'. contradiction.
Qed.

Definition is_valid (m: mem) (b: block) : bool := Pos.ltb b (nextblock m).

Lemma valid_block_iff_is_valid m b : valid_block m b <-> is_valid m b = true.
Proof.
  unfold valid_block, is_valid. split.
  - ii. erewrite Pos.ltb_lt. eauto.
  - ii. erewrite <- Pos.ltb_lt. eauto.
Qed.

Lemma concrete_valid m b addr (CONC: m.(mem_concrete) ! b = Some addr) :
  <<VLD: valid_block m b>>.
Proof.
  r. eapply NNPP. ii. unfold valid_block in H. eapply nextblocks_logical in H. clarify.
Qed.

Local Hint Resolve valid_not_valid_diff: mem.

(** Permissions *)

Definition perm (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission) : Prop :=
   perm_order' (m.(mem_access)#b ofs k) p.

Theorem perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2.
Proof.
  unfold perm, perm_order'; intros.
  destruct (m.(mem_access)#b ofs k); auto.
  eapply perm_order_trans; eauto.
Qed.

Local Hint Resolve perm_implies: mem.

Theorem perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p.
Proof.
  assert (forall po1 po2 p,
          perm_order' po2 p -> perm_order'' po1 po2 -> perm_order' po1 p).
  unfold perm_order', perm_order''. intros.
  destruct po2; try contradiction.
  destruct po1; try contradiction.
  eapply perm_order_trans; eauto.
  unfold perm; intros.
  generalize (access_max m b ofs). eauto.
Qed.

Theorem perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Theorem perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Local Hint Resolve perm_cur perm_max: mem.

Theorem perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b.
Proof.
  unfold perm; intros.
  destruct (plt b m.(nextblock)).
  auto.
  assert (m.(mem_access)#b ofs k = None).
  eapply nextblock_noaccess; eauto.
  rewrite H0 in H.
  contradiction.
Qed.

Local Hint Resolve perm_valid_block: mem.

Remark perm_order_dec:
  forall p1 p2, {perm_order p1 p2} + {~perm_order p1 p2}.
Proof.
  intros. destruct p1; destruct p2; (left; constructor) || (right; intro PO; inversion PO).
Defined.

Remark perm_order'_dec:
  forall op p, {perm_order' op p} + {~perm_order' op p}.
Proof.
  intros. destruct op; unfold perm_order'.
  apply perm_order_dec.
  right; tauto.
Defined.

Theorem perm_dec:
  forall m b ofs k p, {perm m b ofs k p} + {~ perm m b ofs k p}.
Proof.
  unfold perm; intros.
  apply perm_order'_dec.
Defined.

Definition range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p.

Theorem range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Theorem range_perm_cur:
  forall m b lo hi k p,
  range_perm m b lo hi Cur p -> range_perm m b lo hi k p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Theorem range_perm_max:
  forall m b lo hi k p,
  range_perm m b lo hi k p -> range_perm m b lo hi Max p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Local Hint Resolve range_perm_implies range_perm_cur range_perm_max: mem.

Lemma range_perm_dec:
  forall m b lo hi k p, {range_perm m b lo hi k p} + {~ range_perm m b lo hi k p}.
Proof.
  intros.
  induction lo using (well_founded_induction_type (Zwf_up_well_founded hi)).
  destruct (zlt lo hi).
  destruct (perm_dec m b lo k p).
  destruct (H (lo + 1)). red. lia.
  left; red; intros. destruct (zeq lo ofs). congruence. apply r. lia.
  right; red; intros. elim n. red; intros; apply H0; lia.
  right; red; intros. elim n. apply H0. lia.
  left; red; intros. extlia.
Defined.

(** [valid_access m chunk b ofs p] holds if a memory access
    of the given chunk is possible in [m] at address [b, ofs]
    with current permissions [p].
    This means:
- The range of bytes accessed all have current permission [p].
- The offset [ofs] is aligned.
*)

Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ (align_chunk chunk | ofs).

Theorem valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2.
Proof.
  intros. inv H. constructor; eauto with mem.
Qed.

Theorem valid_access_freeable_any:
  forall m chunk b ofs p,
  valid_access m chunk b ofs Freeable ->
  valid_access m chunk b ofs p.
Proof.
  intros.
  eapply valid_access_implies; eauto. constructor.
Qed.

Local Hint Resolve valid_access_implies: mem.

Theorem valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b.
Proof.
  intros. destruct H.
  assert (perm m b ofs Cur Nonempty).
    apply H. generalize (size_chunk_pos chunk). lia.
  eauto with mem.
Qed.

Local Hint Resolve valid_access_valid_block: mem.

Lemma valid_access_perm:
  forall m chunk b ofs k p,
  valid_access m chunk b ofs p ->
  perm m b ofs k p.
Proof.
  intros. destruct H. apply perm_cur. apply H. generalize (size_chunk_pos chunk). lia.
Qed.

Lemma valid_access_compat:
  forall m chunk1 chunk2 b ofs p,
  size_chunk chunk1 = size_chunk chunk2 ->
  align_chunk chunk2 <= align_chunk chunk1 ->
  valid_access m chunk1 b ofs p->
  valid_access m chunk2 b ofs p.
Proof.
  intros. inv H1. rewrite H in H2. constructor; auto.
  eapply Z.divide_trans; eauto. eapply align_le_divides; eauto.
Qed.

Lemma valid_access_dec:
  forall m chunk b ofs p,
  {valid_access m chunk b ofs p} + {~ valid_access m chunk b ofs p}.
Proof.
  intros.
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur p).
  destruct (Zdivide_dec (align_chunk chunk) ofs).
  left; constructor; auto.
  right; red; intro V; inv V; contradiction.
  right; red; intro V; inv V; contradiction.
Defined.

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)
Definition valid_pointer (m: mem) (b: block) (ofs: Z): bool :=
  perm_dec m b ofs Cur Nonempty.

Theorem valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty.
Proof.
  intros. unfold valid_pointer.
  destruct (perm_dec m b ofs Cur Nonempty); simpl;
  intuition congruence.
Qed.

Theorem valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty.
Proof.
  intros. rewrite valid_pointer_nonempty_perm.
  split; intros.
  split. simpl; red; intros. replace ofs0 with ofs by lia. auto.
  simpl. apply Z.divide_1_l.
  destruct H. apply H. simpl. lia.
Qed.

(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

Lemma weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true.
Proof.
  intros. unfold weak_valid_pointer. now rewrite orb_true_iff.
Qed.
Lemma valid_pointer_implies:
  forall m b ofs,
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true.
Proof.
  intros. apply weak_valid_pointer_spec. auto.
Qed.

Lemma captured_valid_in_block
    m b caddr ofs
    (CAPTURED: (mem_concrete m) ! b = Some caddr)
    (VLD: Mem.valid_pointer m b (Ptrofs.unsigned ofs) = true) :
  addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (caddr + Ptrofs.unsigned ofs) b.
Proof.
  econs; eauto; replace (caddr + Ptrofs.unsigned ofs - caddr) with (Ptrofs.unsigned ofs) by lia.
  - rewrite Mem.valid_pointer_nonempty_perm in VLD. eapply Mem.perm_cur_max in VLD.
    unfold Mem.perm, Mem.perm_order' in VLD. des_ifs. eauto.
  - eapply Ptrofs.unsigned_range.
Qed.

Lemma weak_valid_pointer_weak_valid' m b ofs
    (WVLD: Mem.weak_valid_pointer m b ofs = true) :
  Mem._weak_valid_pointer (Mem.mem_access m) b ofs Max.
Proof.
  rewrite Mem.weak_valid_pointer_spec in WVLD. unfold Mem._weak_valid_pointer.
  do 2 rewrite Mem.valid_pointer_nonempty_perm in WVLD. des.
  - left. eapply Mem.perm_cur_max; eauto.
  - right. eapply Mem.perm_cur_max; eauto.
Qed.

Lemma weak_valid_pointer_weak_valid m b ofs
    (WVLD: Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = true) :
  Mem._weak_valid_pointer (Mem.mem_access m) b (Ptrofs.unsigned ofs) Max.
Proof.
  eapply weak_valid_pointer_weak_valid'; eauto.
Qed.

(** * Memory Properties *)

(* [access_le m1 m2] states that the permissions of m1's permission is None each time m2's is *)
Definition access_le (acc1 acc2:PMap.t (Z -> perm_kind -> option permission)): Prop :=
  forall b off (M2_NONE: acc2#b off Max = None),
    acc1#b off Max = None.

Lemma access_le_in_block
    acc1 acc2 concrete addr block
    (WEAK:access_le acc1 acc2)
    (IN_BLOCK_M1: addr_in_block concrete acc1 addr block) :
  addr_in_block concrete acc2 addr block.
Proof.
  intros. unfold access_le in WEAK.
  inversion IN_BLOCK_M1.
  destruct ((acc2#block (addr-caddr) Max)) as [a|] eqn:H.
  + econs. exact CONCRETE. exists a. exact H. eauto.
  + apply WEAK in H. destruct PERM as [a PERM]. simpl in PERM. rewrite PERM in H. inversion H.
Qed.

Lemma access_le_no_overlap:
  forall acc1 acc2 concrete
    (WEAK: access_le acc1 acc2)
    (NO_OVERLAP_M2: forall addr, uniqueness (addr_in_block concrete acc2 addr)),
  forall addr, uniqueness (addr_in_block concrete acc1 addr).
Proof.
  intros. unfold uniqueness in *. intros b1 b2 B1 B2.
  apply NO_OVERLAP_M2 with (addr:=addr);
  apply access_le_in_block with (acc1:=acc1); try exact WEAK;
  try exact B1; try exact B2.
Qed.

Lemma logical_nextblock (m:mem): m.(mem_concrete)!(m.(nextblock)) = None.
Proof.
  apply m.(nextblocks_logical).
  unfold not. intros. apply Plt_ne in H.
  unfold not in H. apply H. reflexivity.
Qed.

(** * Operations over memory stores *)

(** The initial store *)

Program Definition empty: mem :=
  mkmem (PMap.init (ZMap.init Undef))
        (PMap.init (fun ofs k => None))
        (PTree.empty Z)
        1%positive _ _ _ _ _ _ _ _.
Next Obligation.
  repeat rewrite PMap.gi. red; auto.
Qed.
Next Obligation.
  rewrite PMap.gi. auto.
Qed.
Next Obligation.
  rewrite PMap.gi. auto.
Qed.
Next Obligation.
  rewrite PTree.gempty. eauto.
Qed.
Next Obligation.
  inversion IN_BLOCK. des. ss.
  erewrite empty_obligation_2 in PERM. clarify.
Qed.
Next Obligation.
  unfold uniqueness in *. intros b1 b2 B1 B2.
  inversion B1. des. erewrite empty_obligation_2 in PERM. clarify.
Qed.
Next Obligation.
  specialize (RPERM ofs). exploit RPERM; eauto.
  { split; [lia | ]. destruct chunk; ss; lia. }
  ii. des. erewrite empty_obligation_2 in H. clarify.
Qed.
Next Obligation.
  rewrite PTree.gempty in CADDR. clarify.
Qed.

(** Allocation of a fresh block with the given bounds.  Return an updated
  memory state and the address of the fresh block, which initially contains
  undefined cells.  Note that allocation never fails: we model an
  infinite memory. *)

Program Definition alloc (m: mem) (lo hi: Z) :=
  (mkmem (PMap.set m.(nextblock)
                   (ZMap.init Undef)
                   m.(mem_contents))
         (PMap.set m.(nextblock)
                   (fun ofs k => if zle lo ofs && zlt ofs hi then Some Freeable else None)
                   m.(mem_access))
         (m.(mem_concrete))
         (Pos.succ m.(nextblock))
         _ _ _ _ _ _ _ _,
   m.(nextblock)).
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b (nextblock m)).
  subst b. destruct (zle lo ofs && zlt ofs hi); red; auto with mem.
  apply access_max.
Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b (nextblock m)).
  subst b. elim H. apply Plt_succ.
  apply nextblock_noaccess. red; intros; elim H.
  apply Plt_trans_succ; auto.
Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b (nextblock m)). auto. apply contents_default.
Qed.
Next Obligation.
  rewrite m.(nextblocks_logical). reflexivity.
  unfold not in *. intro H0. apply H.
  apply Plt_trans_succ. exact H0.
Qed.
Next Obligation.
  assert (RESULT: addr_in_block m.(mem_concrete) m.(mem_access) addr bo).
  { inversion IN_BLOCK. clear IN_BLOCK.
    destruct (Pos.eq_dec bo m.(nextblock)).
    + rewrite e in CONCRETE. simpl in CONCRETE.
      rewrite logical_nextblock in CONCRETE. inversion CONCRETE.
    + econs. exact CONCRETE.
      destruct PERM as [perm PERM].
      rewrite PMap.gso in PERM.
      exists perm. exact PERM. exact n. eauto. }
  apply m.(valid_address_bounded) in RESULT. exact RESULT.
Qed.
Next Obligation.
  unfold uniqueness in *. intros b1 b2 B1 B2.
  destruct (Pos.eq_dec b1 m.(nextblock)).
  - rewrite e in *. clear B2.
    inversion B1. clear B1. simpl in CONCRETE.
    rewrite logical_nextblock in CONCRETE. inversion CONCRETE.
  - destruct (Pos.eq_dec b2 m.(nextblock)).
    + rewrite e in *. clear B1.
      inversion B2. clear B2. simpl in CONCRETE.
      rewrite logical_nextblock in CONCRETE. inversion CONCRETE.
    + apply m.(no_concrete_overlap) with (addr:=addr);
        [inversion B1 | inversion B2]; simpl in CONCRETE;
          econs; try exact CONCRETE;
          destruct PERM as [perm PERM]; eauto; exists perm;
            rewrite PMap.gso in PERM; try exact PERM; try exact n; try exact n0.
Qed.
Next Obligation.
  assert (b <> (nextblock m)).
  { ii. subst. rewrite logical_nextblock in CADDR. clarify. }
  eapply (concrete_align m); eauto. ii.
  exploit RPERM; eauto. ii. des. rewrite PMap.gso in H1; eauto.
Qed.
Next Obligation.
  eapply weak_valid_address_range; eauto.
  assert (b <> (nextblock m)).
  { ii. subst. rewrite logical_nextblock in CADDR; clarify. }
  unfold _weak_valid_pointer, _valid_pointer in *. rewrite PMap.gso in *; eauto.
Qed.

Definition is_concrete (m: mem) (b: block) : bool :=
  match m.(mem_concrete)!b with
  | Some _ => true
  | _ => false
  end.

Program Definition nonempty_alloc (m: mem) (b: block) (lo hi: Z) :=
  if perm_dec m b lo Max Nonempty then
    Some (mkmem m.(mem_contents)
                (if (is_concrete m b)
                 then m.(mem_access)
                 else (PMap.set b
                         (fun ofs k => if zle lo ofs && zlt ofs hi then Some Nonempty else None)
                         m.(mem_access)))
                m.(mem_concrete)
                m.(nextblock)
                _ _ _ _ _ _ _ _)
  else None.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b).
  - subst. destruct (is_concrete m b) eqn:CONC.
    { apply access_max. }
    rewrite PMap.gss. destruct (zle lo ofs && zlt ofs hi); red; auto with mem.
  - destruct (is_concrete m b) eqn:CONC; eauto.
    { apply access_max. }
    { erewrite PMap.gso; eauto. eapply access_max. }
Qed.
Next Obligation.
  destruct (is_concrete m b) eqn:CONC; eauto.
  { apply nextblock_noaccess. eauto. }
  rewrite PMap.gsspec. destruct (peq b0 b).
  2:{ apply nextblock_noaccess. eauto. }
  des_ifs. exfalso. unfold is_concrete in CONC. des_ifs.
  eapply H0. eapply perm_valid_block; eauto.
Qed.
Next Obligation.
  destruct m; ss.
Qed.
Next Obligation.
  eapply nextblocks_logical. eauto.
Qed.
Next Obligation.
  destruct (peq b bo).
  { subst. inv IN_BLOCK. des. destruct (is_concrete m bo) eqn:CONC.
    - eapply valid_address_bounded with (m:=m) (bo:=bo).
      econs; eauto.
    - unfold is_concrete in CONC. erewrite CONCRETE in CONC. clarify. }
  destruct (is_concrete m b) eqn:CONC.
  { eapply valid_address_bounded with (m:=m) (bo:=bo). eauto. }
  eapply valid_address_bounded with (m:=m) (bo:=bo).
  inv IN_BLOCK. des. rewrite PMap.gso in PERM; eauto. econs; eauto.
Qed.
Next Obligation.
  destruct (is_concrete m b) eqn:CONC.
  { eapply no_concrete_overlap with (m:=m) (addr:=addr). }
  ii. destruct (peq b x); subst.
  { inv H0. exfalso. unfold is_concrete in CONC. des_ifs. }
  destruct (peq b y); subst.
  { inv H1. exfalso. unfold is_concrete in CONC. des_ifs. }
  eapply no_concrete_overlap with (m:=m) (addr:=addr).
  - inv H0. des. rewrite PMap.gso in PERM; eauto. econs; eauto.
  - inv H1. des. rewrite PMap.gso in PERM; eauto. econs; eauto.
Qed.
Next Obligation.
  destruct (is_concrete m b) eqn:CONC.
  { eapply concrete_align; eauto. }
  destruct (peq b b0); subst.
  { exfalso. unfold is_concrete in CONC. des_ifs. }
  eapply concrete_align; eauto. i. eapply RPERM in H0.
  rewrite PMap.gso in H0; eauto.
Qed.
Next Obligation.
  destruct (is_concrete m b) eqn:CONC.
  { eapply weak_valid_address_range; eauto. }
  destruct (peq b b0); subst.
  { exfalso. unfold is_concrete in CONC. des_ifs. }
  eapply weak_valid_address_range; eauto.
  r in WVLD. unfold _valid_pointer in WVLD.
  erewrite PMap.gso in WVLD; eauto.
Qed.

(** the capture of a block is non-deterministic.
    the concrete address that can be given to this block is non-deterministic.
    Thus, we describe with a Proposition.
    [capture m1 b addr m2] states that m2 is the memory m1 at the only difference that the block b has been captured at concrete address addr. *)

Inductive capture (m1:mem) (b:block) (addr:Z) (m2:mem): Prop :=
| capture_intro
    (VALID: valid_block m1 b)
    (CONTENTS: m1.(mem_contents) = m2.(mem_contents))
    (ACCESS: m1.(mem_access) = m2.(mem_access))
    (NEXTBLOCK: m1.(nextblock) = m2.(nextblock))
    (CAPTURED: m1.(mem_concrete)!b = None ->               
               m2.(mem_concrete) = PTree.set b addr m1.(mem_concrete))
    (PREVADDR: forall previous_addr, m1.(mem_concrete)!b = Some previous_addr ->
                            previous_addr = addr /\ m1.(mem_concrete) = m2.(mem_concrete)):
  capture m1 b addr m2.

Inductive capture_list (m1:mem) : list block -> list Z -> mem -> Prop :=
| capture_list_nil :
  capture_list m1 [] [] m1
| capture_list_cons
   b addr m2 bs addrs m3
   (CAP: capture m1 b addr m2)
   (CAPLIST: capture_list m2 bs addrs m3) :
  capture_list m1 (b::bs) (addr::addrs) m3.

Definition valid_block_list (m: mem) (bs: list block) : Prop := Forall (valid_block m) bs. 

Lemma capture_concrete m1 b addr m2
    (CAPTURED: capture m1 b addr m2) :
  <<CONC: m2.(mem_concrete)!b = Some addr>>.
Proof.
  inv CAPTURED.
  destruct (m1.(mem_concrete)!b) eqn:CONC1.
  { exploit PREVADDR; eauto. ii. des; subst. rewrite <- H0. eauto. }
  rewrite CAPTURED0; eauto. rewrite PTree.gss; eauto.
Qed.  

Lemma capture_list_prevaddr m1 b addr bl addrl m2
    (PREVADDR: m1.(mem_concrete) ! b = Some addr)
    (CAPTURED: capture_list m1 bl addrl m2) :
  m2.(mem_concrete) ! b = Some addr.
Proof.
  ginduction bl; ss; i. inv CAPTURED; eauto.
  inv CAPTURED; eauto. eapply IHbl; try eapply CAPLIST; eauto.
  inv CAP; eauto.
  destruct ((mem_concrete m1) ! a) eqn:CAP.
  - exploit PREVADDR0; eauto. i. des. rewrite <- H0; eauto.
  - destruct (peq b a); subst; eauto; clarify.
    erewrite CAPTURED; eauto. erewrite PTree.gso; eauto.
Qed.

Lemma capture_list_concrete m1 bl addrl m2
    (CAPTURED: capture_list m1 bl addrl m2) :
  forall b, In b bl -> exists addr, m2.(mem_concrete)!b = Some addr /\ In addr addrl.
Proof.
  ginduction bl; ss; i.
  inv CAPTURED. exploit capture_concrete; eauto. i. des; subst.
  - exists addr. ss. split; auto. eapply capture_list_prevaddr; eauto.
  - exploit IHbl; eauto. i. des. esplits; eauto. ss. auto.
Qed.  

Lemma capture_list_nextblock m1 bl addrs m2
    (CAP : Mem.capture_list m1 bl addrs m2):
  (nextblock m1) = (nextblock m2).
Proof.
  ginduction bl; ss; i; [inv CAP; eauto|].
  inv CAP. exploit IHbl; eauto. i. erewrite <- H. inv CAP0; eauto.
Qed.

Definition capture_oom (m:mem) (b:block) : Prop :=
  valid_block m b /\ (forall addr m', ~ capture m b addr m').

Definition ptr2int (b:block) (o:Z) (m:mem): option Z :=
  match m.(mem_concrete) ! b with
  | None => None
  | Some caddr => Some (Z.add caddr o)
  end.

Definition ptr2int_v (ptr: val) (m: mem): option val :=
  match ptr with
  | Vptr b ofs => match ptr2int b (Ptrofs.unsigned ofs) m with
                 | Some z => Some (if Archi.ptr64 then Vlong (Int64.repr z) else Vint (Int.repr z))
                 | _ => None
                 end
  | _ => None
  end.

Lemma ptr2int_weak_valid_aux b ofs m addr
    (PTR2INT: ptr2int b ofs m = Some addr)
    (WVLD: _weak_valid_pointer (mem_access m) b ofs Max)
    (RANGE: 0 <= ofs <= Ptrofs.max_unsigned) :
  exists caddr, <<INRANGE: in_range addr (1, Ptrofs.modulus)>>
         /\ <<CONC: (mem_concrete m) ! b = Some caddr>>
         /\ <<OFS: addr = caddr + ofs>>.
Proof.
  unfold ptr2int in PTR2INT. des_ifs. esplits; eauto.
  eapply weak_valid_address_range; eauto.
  unfold Ptrofs.max_unsigned in RANGE. lia.
Qed.

Lemma ptr2int_weak_valid b ofs m addr
    (PTR2INT: ptr2int b ofs m = Some addr)
    (WVLD: weak_valid_pointer m b ofs = true)
    (RANGE: 0 <= ofs <= Ptrofs.max_unsigned) :
  in_range addr (1, Ptrofs.modulus).
Proof.
  eapply weak_valid_pointer_weak_valid' in WVLD.
  unfold ptr2int in PTR2INT. des_ifs.
  eapply weak_valid_address_range; eauto.
  unfold Ptrofs.max_unsigned in RANGE. lia.
Qed.

Lemma ptr2int_weak_valid' b ofs m addr
    (PTR2INT: ptr2int b ofs m = Some addr)
    (WVLD: weak_valid_pointer m b ofs = true)
    (RANGE: 0 <= ofs <= Ptrofs.max_unsigned) :
  exists caddr, <<INRANGE: in_range addr (1, Ptrofs.modulus)>>
         /\ <<CONC: (mem_concrete m) ! b = Some caddr>>
         /\ <<OFS: addr = caddr + ofs>>.
Proof.
  eapply weak_valid_pointer_weak_valid' in WVLD.
  eapply ptr2int_weak_valid_aux; eauto.
Qed.

Lemma ptr2int_not_nullptr32 z m b ofs
    (BIT: Archi.ptr64 = false)
    (PTR2INT: ptr2int b ofs m = Some z)
    (WVLD: weak_valid_pointer m b ofs = true)
    (RANGE: 0 <= ofs <= Ptrofs.max_unsigned) :
  <<NOTNULL: Int.eq (Int.repr z) Int.zero = false>>.
Proof.
  exploit ptr2int_weak_valid'; eauto. i. des. subst. inv INRANGE. simpl in *.
  eapply Ptrofs.modulus_eq32 in BIT. unfold Ptrofs.max_unsigned in *. rewrite BIT in *.
  unfold Int.eq. rewrite Int.unsigned_repr; [|unfold Int.max_unsigned; lia].
  rewrite Int.unsigned_zero. des_ifs; lia.
Qed.

Lemma ptr2int_not_nullptr64 z m b ofs
    (BIT: Archi.ptr64 = true)
    (PTR2INT: ptr2int b ofs m = Some z)
    (WVLD: weak_valid_pointer m b ofs = true)
    (RANGE: 0 <= ofs <= Ptrofs.max_unsigned) :
  <<NOTNULL: Int64.eq (Int64.repr z) Int64.zero = false>>.
Proof.
  exploit ptr2int_weak_valid'; eauto. i. des. subst. inv INRANGE. simpl in *.
  eapply Ptrofs.modulus_eq64 in BIT. unfold Ptrofs.max_unsigned in *. rewrite BIT in *.
  unfold Int64.eq. rewrite Int64.unsigned_repr; [|unfold Int64.max_unsigned; lia].
  rewrite Int64.unsigned_zero. des_ifs; lia.
Qed.

Lemma ptr2int_not_nullptr64_max z m b ofs
    (BIT: Archi.ptr64 = true)
    (PTR2INT: ptr2int b ofs m = Some z)
    (WVLD: _weak_valid_pointer (mem_access m) b ofs Max)
    (RANGE: 0 <= ofs <= Ptrofs.max_unsigned) :
  <<NOTNULL: Int64.eq (Int64.repr z) Int64.zero = false>>.
Proof.
  exploit ptr2int_weak_valid_aux; eauto. i. des. subst. inv INRANGE. simpl in *.
  eapply Ptrofs.modulus_eq64 in BIT. unfold Ptrofs.max_unsigned in *. rewrite BIT in *.
  unfold Int64.eq. rewrite Int64.unsigned_repr; [|unfold Int64.max_unsigned; lia].
  rewrite Int64.unsigned_zero. des_ifs; lia.
Qed.

(** reverse function of capture for int to ptr casting *)

Definition denormalize_aux :=
  fun i m b =>
    match m.(mem_concrete) ! b with
    | Some caddr => if ((is_valid m b) && (addr_is_in_block m.(mem_concrete) m.(mem_access) i b))
                   then Some (b, Z.sub i caddr) else None
    | _ => None
    end.

Definition denormalize (i: Z) (m:mem): option (block * Z) :=
  PTree.select (fun b _ => denormalize_aux i m b) m.(mem_concrete).

Definition to_valid (v: val) (m:mem) : option val :=
  match v with
  | Vint n => if negb Archi.ptr64
             then (match denormalize (Int.unsigned n) m with
                   | Some (b, ofs) => Some (Vptr b (Ptrofs.repr ofs))
                   | _ => None
                   end)
             else None
  | Vlong n => if Archi.ptr64
              then (match denormalize (Int64.unsigned n) m with
                    | Some (b, ofs) => Some (Vptr b (Ptrofs.repr ofs))
                    | _ => None
                    end)
              else None
  | _ => None
  end.

Definition to_int (v: val) (m: mem) : option val :=
  match v with
  | Vptr b ofs => ptr2int_v (Vptr b ofs) m
  | Vint n => Some (Vint n) (* Vtrue, Vfalse always "Vint" *) (* if negb Archi.ptr64 then Some (Vint n) else None *)
  | Vlong n => Some (Vlong n) (* if Archi.ptr64 then Some (Vlong n) else None *)
  | _ => None
  end.

Definition denormalize_to_val (z: Z) (m: mem) : option val :=
  match denormalize z m with
  | Some (b, ofs) => Some (Vptr b (Ptrofs.repr ofs))
  | _ => None
  end.

Definition to_ptr (v: val) (m: mem) : option val :=
  match v with
  | Vptr b ofs => Some (Vptr b ofs)
  | Vint n => if negb Archi.ptr64
             then (if (Int.eq n Int.zero)
                   then Some Vnullptr
                   else (match denormalize (Int.unsigned n) m with
                         | Some (b, ofs) => Some (Vptr b (Ptrofs.repr ofs))
                         | _ => None
                         end))
             else None
  | Vlong n => if Archi.ptr64
              then (if (Int64.eq n Int64.zero)
                    then Some Vnullptr
                    else (match denormalize (Int64.unsigned n) m with
                          | Some (b, ofs) => Some (Vptr b (Ptrofs.repr ofs))
                          | _ => None
                          end))
             else None
  | _ => None
  end.

Lemma denormalize_in_range z m b ofs
    (DENO: denormalize z m = Some (b, ofs)) :
  <<INRANGE: 0 <= ofs < Ptrofs.modulus>>.
Proof.
  eapply PTree.gselectf in DENO. des.
  unfold denormalize_aux in DENO0. des_ifs.
  eapply andb_prop in Heq0. des.
  unfold addr_is_in_block in Heq1. des_ifs. rr. lia.
Qed.

Lemma denormalize_paddr_in_range z m b ofs
    (DENO: denormalize z m = Some (b, ofs)) :
  <<INRANGE: in_range z (1, Ptrofs.modulus - 1)>>.
Proof.
  eapply PTree.gselectf in DENO. des. unfold denormalize_aux in DENO0. des_ifs.
  eapply andb_prop in Heq0. des. rewrite <- addr_in_block_iff in Heq1.
  exploit _valid_pointer_range; eauto.
Qed.

Lemma denormalize_not_in_range m z
    (NOTRANGE: ~ in_range z (1, Ptrofs.modulus - 1)) :
  <<DENOFAIL: denormalize z m = None>>.
Proof.
  destruct (denormalize z m) eqn: DENO; eauto.
  exfalso. destruct p. eapply NOTRANGE. eapply denormalize_paddr_in_range; eauto.
Qed.

Lemma denormalize_nullptr m : <<DENOFAIL: denormalize 0 m = None>>.
Proof. eapply denormalize_not_in_range; eauto. ii. inv H; ss. Qed.

Lemma denormalize_perm z m b ofs
    (DENO: denormalize z m = Some (b, ofs)) :
  <<PERM: exists p, perm m b ofs Max p>>.
Proof.
  eapply PTree.gselectf in DENO. des.
  unfold denormalize_aux in DENO0. des_ifs.
  eapply andb_prop in Heq0. des. unfold addr_is_in_block in Heq1. des_ifs.
  r. exists p. unfold perm, perm_order'. rewrite Heq. eapply perm_refl.
Qed.

Lemma to_ptr_nullptr m :
  <<TOPTRFAIL: to_ptr Vnullptr m = Some Vnullptr>>.
Proof. unfold to_ptr. des_ifs. Qed.

Lemma denormalize_info z m b ofs
  (DENO: denormalize z m = Some (b, ofs)) :
  exists caddr, <<VBLK: valid_block m b>>
         /\ <<CONC: (mem_concrete m)!b = Some caddr>>
         /\ <<OFS: ofs = z - caddr>>
         /\ <<PERM: perm m b ofs Max Nonempty>>
         /\ <<ORANGE: 0 <= ofs <= Ptrofs.max_unsigned>>
         /\ <<CRANGE: 1 <= z < Ptrofs.max_unsigned>>.
Proof.
  exploit denormalize_perm; eauto. i.
  exploit denormalize_paddr_in_range; eauto. i.
  exploit denormalize_in_range; eauto. i. des.
  eapply PTree.gselectf in DENO. des.
  unfold denormalize_aux in DENO0. des_ifs.
  eapply andb_prop in Heq0. des. rewrite <- addr_in_block_iff in Heq1.
  inv Heq1. des. clarify. esplits; eauto.
  - eapply NNPP. ii. eapply nextblocks_logical in H3. clarify.
  - unfold perm. rewrite PERM. eapply perm_any_N.
  - unfold Ptrofs.max_unsigned. lia.
  - inv H0; eauto.
  - inv H0. unfold snd in SND. unfold Ptrofs.max_unsigned. lia.
Qed.

Lemma conditions_of_addr_in_block m b caddr addr
    (CONC: (Mem.mem_concrete m)!b = Some caddr)
    (PERM: Mem.perm m b (addr - caddr) Max Nonempty)
    (RANGE: 0 <= addr - caddr <= Ptrofs.max_unsigned) :
  <<INBLK: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) addr b>>.
Proof.
  unfold Ptrofs.max_unsigned in RANGE. econs; eauto; [|lia].
  unfold Mem.perm, Mem.perm_order' in PERM. des_ifs. eauto.
Qed.

Lemma ptr2int_to_denormalize_max b ofs m z
    (P2I: Mem.ptr2int b ofs m = Some z)
    (RANGE: 0 <= ofs <= Ptrofs.max_unsigned)
    (VLD: perm m b ofs Max Nonempty) :
  <<DENO: Mem.denormalize z m = Some (b, ofs)>>.
Proof.
  exploit Mem.ptr2int_weak_valid_aux; eauto.
  { unfold _weak_valid_pointer. unfold _valid_pointer, perm in *. eauto. }
  i. des. subst.
  destruct (Mem.denormalize (caddr + ofs) m) eqn:DENO.
  - destruct p. eapply PTree.gselectf in DENO. i. des.
    unfold Mem.denormalize_aux in DENO0. des_ifs.
    eapply andb_prop in Heq0. des. rewrite <- Mem.addr_in_block_iff in Heq1.
    assert (INBLK: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (caddr + ofs) b).
    { eapply conditions_of_addr_in_block; eauto;[|lia].
      replace (caddr + ofs - caddr) with ofs by lia. eauto. }
    assert (b0 = b) by (eapply Mem.no_concrete_overlap; eauto).
    subst. clarify. replace (caddr + ofs - caddr) with ofs by lia. eauto.
  - eapply PTree.gselectnf in DENO. exfalso. eapply DENO. esplits; eauto.
    ii. unfold Mem.denormalize_aux in *. des_ifs. rewrite andb_false_iff in Heq0. des.
    { rewrite Mem.nextblocks_logical in *; clarify. ii.
      assert (Mem.valid_block m b); eauto. rewrite Mem.valid_block_iff_is_valid in H1. clarify. }
    { unfold Mem.addr_is_in_block in *. des_ifs.
      - unfold Ptrofs.max_unsigned in RANGE0. lia.
      - replace (caddr + ofs - caddr) with ofs in Heq by lia.
        unfold Mem.perm in VLD. rewrite Heq in VLD. ss. }
Qed.

Lemma ptr2int_to_denormalize b ofs m z
    (P2I: ptr2int b ofs m = Some z)
    (RANGE: 0 <= ofs <= Ptrofs.max_unsigned)
    (VLD: valid_pointer m b ofs = true) :
  <<DENO: denormalize z m = Some (b, ofs)>>.
Proof.
  rewrite valid_pointer_nonempty_perm in VLD. eapply perm_cur_max in VLD.
  eapply ptr2int_to_denormalize_max; eauto.
Qed.

Lemma denormalized_not_nullptr32 z m b ofs
    (BIT: Archi.ptr64 = false)
    (DENO: denormalize z m = Some (b, ofs)) :
  <<NOTNULL: Int.eq (Int.repr z) Int.zero = false>>.
Proof.
  eapply denormalize_info in DENO. des. subst.
  eapply Ptrofs.modulus_eq32 in BIT. unfold Ptrofs.max_unsigned in *. rewrite BIT in *.
  unfold Int.eq. rewrite Int.unsigned_repr; [|unfold Int.max_unsigned; lia].
  des_ifs; lia.
Qed.

Lemma denormalized_not_nullptr64 z m b ofs
  (BIT: Archi.ptr64 = true)
  (DENO: denormalize z m = Some (b, ofs)) :
  <<NOTNULL: Int64.eq (Int64.repr z) Int64.zero = false>>.
Proof.
  eapply denormalize_info in DENO. des. subst.
  eapply Ptrofs.modulus_eq64 in BIT. unfold Ptrofs.max_unsigned in *. rewrite BIT in *.
  unfold Int64.eq. rewrite Int64.unsigned_repr; [|unfold Int64.max_unsigned; lia].
  des_ifs; lia.
Qed.

(* Definition bo2val (bo: block * Z) : val := *)
(*   Vptr (fst bo) (Ptrofs.repr (snd bo)). *)

(* (* val2ptr v m = [exact pointer; weak valid pointer; *) *)
(* Definition val2ptr (v:val) (m:mem) : list val := *)
(*   match v with *)
(*   | Vint n => *)
(*       if Archi.ptr64 *)
(*       then [] *)
(*       else map bo2val (addr2ptr (Int.intval n) m) *)
(*   | Vlong n => *)
(*       if Archi.ptr64 *)
(*       then map bo2val (addr2ptr (Int64.intval n) m) *)
(*       else [] *)
(*   | Vptr b ofs => [(Vptr b ofs)] *)
(*   | _ => [] *)
(*   end *)
(* . *)

(* Lemma addr2ptr_length *)
(*   z m pl *)
(*   (A2P: addr2ptr z m = pl) *)
(*   : *)
(*   <<PLEN: (length pl <= 2)%nat>>. *)
(* Proof. *)
(*   unfold addr2ptr in A2P. des_ifs; rr; ss; try lia. *)
(* Qed. *)

(* Lemma val2ptr_length *)
(*   v m pl *)
(*   (V2P: val2ptr v m = pl) *)
(*   : *)
(*   <<PLEN: (length pl <= 2)%nat>>. *)
(* Proof. *)
(*   unfold val2ptr in V2P. des_ifs; rr; ss; try lia. *)
(*   unfold addr2ptr. des_ifs; ss; try lia. *)
(* Qed. *)

(* Lemma addr2ptr_nullptr *)
(*   m *)
(*   : *)
(*   <<NONE: addr2ptr 0 m = []>>. *)
(* Proof. *)
(*   unfold addr2ptr in *. des_ifs; try (rewrite denormalize_nullptr in Heq; clarify). *)
(*   erewrite denormalize_not_in_range in Heq0; clarify. ii. inv H; ss. *)
(* Qed. *)

(* Lemma val2ptr_nullptr *)
(*   m *)
(*   : *)
(*   <<NONE: val2ptr Vnullptr m = []>>. *)
(* Proof. *)
(*   unfold Vnullptr, val2ptr. des_ifs. destruct (addr2ptr (Int64.intval Int64.zero) m) eqn: A2P; ss. *)
(*   replace (Int64.intval Int64.zero) with (Int64.unsigned Int64.zero) in A2P; cycle 1. *)
(*   { unfold Int64.unsigned. ss. } *)
(*   erewrite Int64.unsigned_zero in A2P. rewrite addr2ptr_nullptr in A2P. clarify. *)
(* Qed. *)

(* Lemma addr2ptr_valid_weak_valid *)
(*   z m b1 ofs1 b2 ofs2 *)
(*   (V2P: addr2ptr z m = [(b1, ofs1); (b2, ofs2)]) *)
(*   : *)
(*     <<VLD: valid_pointer m b1 ofs1 = true>> *)
(*   /\ <<WVLD1: weak_valid_pointer m b2 ofs2 = true>> *)
(*   /\ <<WVLD2: valid_pointer m b2 ofs2 = false>> *)
(* . *)
(* Proof. *)
(*   unfold addr2ptr in *. des_ifs. *)
(*   eapply PTree.gselectf in Heq, Heq0. des. *)
(*   unfold denormalize_aux in *. des_ifs. *)
(*   eapply andb_prop in Heq, Heq0. des. *)
(*   replace (z - 1 - a + 1) with (z - a) by lia. *)
(*   esplits. *)
(*   { unfold addr_is_in_block in Heq5. des_ifs. *)
(*     rewrite valid_pointer_nonempty_perm. *)
(*     unfold perm, perm_order'. *)
(*     rewrite Heq2. eapply perm_any_N. } *)
(*   { rewrite weak_valid_pointer_spec. *)
(*     right. unfold addr_is_in_block in Heq3. des_ifs. *)
(*     replace (z - a - 1) with (z - 1 - a) by lia. *)
(*     rewrite valid_pointer_nonempty_perm.  *)
(*     unfold perm, perm_order'. des_ifs. *)
(*     eapply perm_any_N. } *)
(*   { destruct (valid_pointer m b2 (z - a)) eqn:VLD; eauto. *)
(*     rewrite valid_pointer_nonempty_perm in VLD. *)
(*     exfalso. *)
(*     unfold perm, perm_order' in VLD. des_ifs. *)
(*     assert (INBLK:addr_in_block (mem_concrete m) (mem_access m) z b2). *)
(*     { econs; eauto. unfold in_rangeb in Heq1. ss. des_ifs. lia. } *)
(*     rewrite <- addr_in_block_iff in Heq5. *)
(*     exploit no_concrete_overlap. *)
(*     { eapply Heq5. } *)
(*     { eapply INBLK. } *)
(*     ii. clarify. } *)
(* Qed. *)

(* Lemma val2ptr_valid_weak_valid *)
(*   v m b1 ofs1 b2 ofs2 *)
(*   (V2P: val2ptr v m = [Vptr b1 ofs1; Vptr b2 ofs2]) *)
(*   : *)
(*     <<VLD: valid_pointer m b1 (Ptrofs.unsigned ofs1) = true>> *)
(*   /\ <<WVLD1: weak_valid_pointer m b2 (Ptrofs.unsigned ofs2) = true>> *)
(*   /\ <<WVLD2: valid_pointer m b2 (Ptrofs.unsigned ofs2) = false>> *)
(* . *)
(* Proof. *)
(*   destruct v; ss. des_ifs. *)
(*   remember (addr2ptr (Int64.intval i) m) as pl. symmetry in Heqpl. *)
(*   do 3 (destruct pl; ss). destruct p; destruct p0. clarify. *)
(*   exploit addr2ptr_valid_weak_valid; eauto. *)
(*   unfold addr2ptr in *. des_ifs. ii. des. *)
(*   eapply denormalize_in_range in Heq0. unfold in_rangeb in *. ss. des_ifs. des. *)
(*   esplits; rewrite Ptrofs.unsigned_repr; eauto; unfold max_address, Ptrofs.max_unsigned in *; lia. *)
(* Qed. *)

(* Lemma addr2ptr_permission *)
(*   z m b1 ofs1 b2 ofs2 *)
(*   (V2P: addr2ptr z m = [(b1, ofs1); (b2, ofs2)]) *)
(*   : *)
(*     <<PERMVLD: Mem.perm m b1 ofs1 Cur Nonempty>> *)
(*   /\ <<PERMWVLD: ~ Mem.perm m b2 ofs2 Cur Nonempty>>. *)
(* Proof. *)
(*   exploit (addr2ptr_valid_weak_valid z m b1 ofs1 b2 ofs2); eauto. *)
(*   i. des. esplits. *)
(*   { rewrite <- valid_pointer_nonempty_perm. eauto. } *)
(*   { ii. rewrite <- valid_pointer_nonempty_perm in H. clarify. } *)
(* Qed. *)

(* Lemma val2ptr_permission *)
(*   v m b1 ofs1 b2 ofs2 *)
(*   (V2P: val2ptr v m = [Vptr b1 ofs1; Vptr b2 ofs2]) *)
(*   : *)
(*     <<PERMVLD: Mem.perm m b1 (Ptrofs.unsigned ofs1) Cur Nonempty>> *)
(*   /\ <<PERMWVLD: ~ Mem.perm m b2 (Ptrofs.unsigned ofs2) Cur Nonempty>>. *)
(* Proof. *)
(*   exploit (val2ptr_valid_weak_valid v m b1 ofs1 b2 ofs2); eauto. *)
(*   i. des. esplits. *)
(*   { rewrite <- valid_pointer_nonempty_perm. eauto. } *)
(*   { ii. rewrite <- valid_pointer_nonempty_perm in H. clarify. } *)
(* Qed. *)

(* Lemma val2ptr_permission_valid *)
(*   v m b ofs *)
(*   (V2P: In (Vptr b ofs) (val2ptr v m)) *)
(*   (PERM: perm m b (Ptrofs.unsigned ofs) Cur Nonempty) *)
(*   : *)
(*   exists pl, <<V2P: val2ptr v m = (Vptr b ofs)::pl>> *)
(* . *)
(* Proof. *)
(*   destruct (Mem.val2ptr v m) eqn:V2P'; ss. *)
(*   destruct l; ss. *)
(*   { des; clarify. esplits; eauto. } *)
(*   destruct l; ss. *)
(*   2:{ eapply Mem.val2ptr_length in V2P'. inv V2P'. inv H0. inv H1. } *)
(*   des; clarify. *)
(*   { esplits; eauto. } *)
(*   assert (exists b0 ofs0, v0 = Vptr b0 ofs0). *)
(*   { unfold val2ptr, addr2ptr, bo2val in *; des_ifs; ss. clarify. eauto. } *)
(*   des; subst. eapply val2ptr_permission in V2P'. des; clarify. *)
(* Qed. *)

(* Lemma addr2ptr_different_block *)
(*   z m b1 ofs1 b2 ofs2 *)
(*   (V2P: addr2ptr z m = [(b1, ofs1); (b2, ofs2)]) *)
(*   : *)
(*   <<DFFBLK: b1 <> b2>> *)
(* . *)
(* Proof. unfold addr2ptr in V2P. des_ifs. Qed. *)

(* Lemma val2ptr_different_block *)
(*   z m b1 ofs1 b2 ofs2 *)
(*   (V2P: val2ptr z m = [Vptr b1 ofs1; Vptr b2 ofs2]) *)
(*   : *)
(*   <<DFFBLK: b1 <> b2>> *)
(* . *)
(* Proof. unfold val2ptr, addr2ptr, bo2val in V2P. des_ifs; ss. clarify. Qed. *)

Lemma Z_sub_reg_r (a b c:Z)
    (SUB: a - c = b - c) : a = b.
Proof.
  do 2 rewrite <- Z.add_opp_r in SUB.
  rewrite Z.add_comm in SUB. rewrite (Z.add_comm b) in SUB.
  eapply Z.add_reg_l; eauto.
Qed.

(* Lemma denormalize_same_addr *)
(*   i1 i2 m b o *)
(*   (DENO1: denormalize i1 m = Some (b, o)) *)
(*   (DENO2: denormalize i2 m = Some (b, o)) : *)
(*   <<SAMEADD: i1 = i2>>. *)
(* Proof. *)
(*   eapply PTree.gselectf in DENO1, DENO2. *)
(*   des. unfold denormalize_aux in *. des_ifs. *)
(*   eapply Z_sub_reg_r; eauto. *)
(* Qed. *)
  
(* Lemma addr2ptr_same_addr *)
(*   i1 i2 m pl *)
(*   (A2P1: addr2ptr i1 m = pl) *)
(*   (A2P2: addr2ptr i2 m = pl) *)
(*   (LEN: Zlength pl >= 1) *)
(*   : *)
(*   <<SAMEADD: i1 = i2>>. *)
(* Proof. *)
(*   dup A2P1. dup A2P2. *)
(*   unfold addr2ptr in A2P1, A2P2. *)
(*   des_ifs; (try (by (eapply denormalize_same_addr; eauto))). *)
(*   { eapply PTree.gselectf in Heq, Heq2. *)
(*     des. unfold denormalize_aux in *. des_ifs. *)
(*     eapply andb_prop in Heq2, Heq. des. *)
(*     replace (i1 - 1 - a0 + 1) with (i1 - a0) in H0 by lia. *)
(*     eapply Z_sub_reg_r; eauto. } *)
(*   { eapply PTree.gselectnf in Heq2. *)
(*     assert (~ perm m b1 (z1 + 1) Cur Nonempty). *)
(*     { clear - Heq2 Heq3 Heq4. *)
(*       ii. eapply PTree.gselectf in Heq3. des. *)
(*       eapply Heq2. esplits; eauto. ii. *)
(*       clear Heq2. *)
(*       unfold denormalize_aux in *. des_ifs. *)
(*       eapply andb_prop in Heq2. des. *)
(*       rewrite andb_false_iff in Heq1. des; clarify. *)
(*       replace (i1 - 1 - a + 1) with (i1 - a) in Heq4, H by lia. *)
(*       unfold addr_is_in_block in Heq1. des_ifs. *)
(*       { unfold in_rangeb in Heq4. des_ifs. ss. lia. } *)
(*       unfold perm, perm_order' in H. rewrite Heq in H. clarify. } *)
(*     exfalso. eapply H. eapply denormalize_perm in Heq. des. *)
(*     eapply perm_implies; eauto. eapply perm_any_N. } *)
(*   { eapply PTree.gselectf in Heq, Heq2. *)
(*     des. unfold denormalize_aux in *. des_ifs. *)
(*     eapply andb_prop in Heq2, Heq. des. *)
(*     replace (i1 - 1 - a0 + 1) with (i1 - a0) in H0 by lia. *)
(*     eapply Z_sub_reg_r; eauto. } *)
(*   { eapply PTree.gselectnf in Heq. *)
(*     assert (~ perm m b1 (z + 1) Cur Nonempty). *)
(*     { clear - Heq Heq0 Heq1. *)
(*       ii. eapply PTree.gselectf in Heq0. des. *)
(*       eapply Heq. esplits; eauto. ii. *)
(*       clear Heq. *)
(*       unfold denormalize_aux in *. des_ifs. *)
(*       eapply andb_prop in Heq3. des. *)
(*       rewrite andb_false_iff in Heq0. des; clarify. *)
(*       replace (i2 - 1 - a + 1) with (i2 - a) in Heq1, H by lia. *)
(*       unfold addr_is_in_block in Heq0. des_ifs. *)
(*       { unfold in_rangeb in Heq1. des_ifs. ss. lia. } *)
(*       unfold perm, perm_order' in H. rewrite Heq in H. clarify. } *)
(*     exfalso. eapply H. eapply denormalize_perm in Heq2. des. *)
(*     eapply perm_implies; eauto. eapply perm_any_N. } *)
(*   { eapply PTree.gselectf in Heq2, Heq3, Heq0. *)
(*     des. unfold denormalize_aux in *. des_ifs. *)
(*     eapply andb_prop in Heq2, Heq3, Heq0. des. *)
(*     replace (i2 - 1 - a1 + 1) with (i2 - a1) in H0 by lia. *)
(*     eapply Z_sub_reg_r; eauto. } *)
(*   { eapply PTree.gselectf in Heq2, Heq0. *)
(*     des. unfold denormalize_aux in *. des_ifs. *)
(*     eapply andb_prop in Heq2, Heq0. des. *)
(*     replace (i2 - 1 - a0 + 1) with (i2 - a0) in H0 by lia. *)
(*     eapply Z_sub_reg_r; eauto. } *)
(*   { assert (z = z0) by lia. *)
(*     subst. eapply (Z_sub_reg_r _ _ 1) . *)
(*     eapply denormalize_same_addr; eauto. } *)
(* Qed. *)

(* Definition ptr2val (ptr: block * ptrofs) : val := Vptr (fst ptr) (snd ptr). *)

(** Freeing a block between the given bounds.
  Return the updated memory state where the given range of the given block
  has been invalidated: future reads and writes to this
  range will fail.  Requires freeable permission on the given range. *)

Program Definition unchecked_free (m: mem) (b: block) (lo hi: Z): mem :=
  mkmem m.(mem_contents)
        (PMap.set b
                (fun ofs k => if zle lo ofs && zlt ofs hi then None else m.(mem_access)#b ofs k)
                m.(mem_access))
        m.(mem_concrete)
        m.(nextblock)
        _ _ _ _ _ _ _ _.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b).
  destruct (zle lo ofs && zlt ofs hi). red; auto. apply access_max.
  apply access_max.
Qed.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b). subst.
  destruct (zle lo ofs && zlt ofs hi). auto. apply nextblock_noaccess; auto.
  apply nextblock_noaccess; auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  apply m.(nextblocks_logical). exact H.
Qed.
Next Obligation.
  eapply m.(valid_address_bounded).
  inversion IN_BLOCK.
  econs.
  exact CONCRETE.
  destruct (Pos.eq_dec bo b).
  - rewrite e in *. rewrite PMap.gss in PERM.
    destruct PERM as [perm PERM]. simpl in PERM.
    destruct (zle lo (addr - caddr) && zlt (addr - caddr) hi); try inversion PERM. exists perm. simpl. exact H0.
  - rewrite PMap.gso in PERM. exact PERM. exact n.
  - eauto.
Qed.
Next Obligation.
  unfold uniqueness in *. intros b1 b2 B1 B2.
  apply access_le_no_overlap with (acc2:=m.(mem_access)) (concrete:=m.(mem_concrete)) (addr:=addr) (acc1:=(PMap.set b (fun (ofs : Z) (k : perm_kind) => if zle lo ofs && zlt ofs hi then None else (mem_access m) # b ofs k) (mem_access m))).
  - unfold access_le. intros.
    destruct (Pos.eq_dec b0 b).
    + rewrite e in *. rewrite PMap.gss.
      destruct(zle lo off && zlt off hi); try reflexivity; try exact M2_NONE.
    + rewrite PMap.gso; try exact n; try exact M2_NONE.
  - apply m.(no_concrete_overlap).
  - exact B1. - exact B2.
Qed.
Next Obligation.
  eapply concrete_align; eauto. ii.
  exploit RPERM; eauto. ii. des.
  destruct (peq b b0); subst.
  - rewrite PMap.gss in H0; eauto.
    des_ifs; clarify; eauto.
  - rewrite PMap.gso in H0; eauto.
Qed.
Next Obligation.
  eapply weak_valid_address_range; eauto.
  destruct (Pos.eq_dec b0 b); subst; unfold _weak_valid_pointer, _valid_pointer in *.
  2: { rewrite PMap.gso in WVLD; eauto. }
  subst. rewrite PMap.gss in WVLD; eauto.
  des_ifs; des; clarify; eauto.
Qed.

Definition free (m: mem) (b: block) (lo hi: Z): option mem :=
  if range_perm_dec m b lo hi Cur Freeable
  then Some(unchecked_free m b lo hi)
  else None.

Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

(** Memory reads. *)

(** Reading N adjacent bytes in a block content. *)

Fixpoint getN (n: nat) (p: Z) (c: ZMap.t memval) {struct n}: list memval :=
  match n with
  | O => nil
  | S n' => ZMap.get p c :: getN n' (p + 1) c
  end.

Definition val2chunk (v:val): memory_chunk :=
  match v with
  | Vint _ => Mint32
  | Vlong _ => Mint64
  | Vptr _ _ => Mptr
  | _ => if Archi.ptr64 then Many64 else Many32
  end.

Definition _decode_normalize_mv := fun m mv => match mv with
                                             | Fragment v q n =>
                                                 match (Mem.to_int v m) with
                                                 | Some v' =>
                                                     match (nth_error (rev_if_be_mv (encode_val (val2chunk v') v')) n) with
                                                     | Some b => b
                                                     | None => mv
                                                     end
                                                 | None => mv
                                                 end
                                             | _ => mv
                                             end.

Definition is_intptr_mv (mv:memval) : bool :=
  match mv with
  | Fragment v q n =>
      match v with
      | Vint _ => negb Archi.ptr64 && quantity_eq q Q32 (* && Nat.ltb n 4 *)
      | Vlong _ => Archi.ptr64 && quantity_eq q Q64 (* && Nat.ltb n 8 *)
      | _ => false
      end
  | _ => false
  end.

Definition qarchi := if Archi.ptr64 then Q64 else Q32.

Definition is_ptrlike_mv (mv: memval) : bool :=
  is_intptr_mv mv || is_ptr_mv mv || is_byte_mv mv.

Definition is_mixed_mvs (mvs: list memval) : bool :=
  forallb is_ptrlike_mv mvs && (negb (forallb is_ptr_mv mvs)).

Definition is_mixed_mvs_old (mvs: list memval) : bool :=
  forallb is_ptrlike_mv mvs && (negb (forallb is_byte_mv mvs)) && (negb (forallb is_ptr_mv mvs)) && (negb (forallb is_intptr_mv mvs)).

Lemma inj_bytes_all_bytes bl (LEN: (Datatypes.length bl > 0)%nat):
  <<NOFRAG: forallb is_byte_mv (inj_bytes bl) = true>>.
Proof. destruct bl; ss. ginduction bl; ss. i. eapply IHbl; eauto. ss. lia. Qed.

(* merge *)
Lemma inj_bytes_all_bytes' bl:
  <<NOFRAG: forallb is_byte_mv (inj_bytes bl) = true>>.
Proof. destruct bl; ss. ginduction bl; ss. Qed.

Lemma inj_bytes_no_fragment v q n bl (LEN: (Datatypes.length bl > 0)%nat):
  <<NOFRAG: ~ In (Fragment v q n) (inj_bytes bl)>>.
Proof.
  ii. exploit inj_bytes_all_bytes; eauto. i. des. rewrite forallb_forall in H0.
  eapply H0 in H. ss.
Qed.

Lemma inj_bytes_no_fragment' v q n bl:
  <<NOFRAG: ~ In (Fragment v q n) (inj_bytes bl)>>.
Proof.
  ii. exploit inj_bytes_all_bytes'; eauto. i. des. rewrite forallb_forall in H0.
  eapply H0 in H. ss.
Qed.

Definition normalize_check (chunk: memory_chunk) (mvs: list memval) : bool :=
  match chunk with
  | Mint64 | Many64 => Archi.ptr64 && (is_mixed_mvs mvs)
  | Mint32 | Many32 => (negb Archi.ptr64) && (is_mixed_mvs mvs)
  | _ => false
  end.
  

Definition normalize_mvs (chunk: memory_chunk) (m: mem) (mvs: list memval) : (list memval) :=
  if (normalize_check chunk mvs) then map (_decode_normalize_mv m) mvs else mvs.

Lemma normalize_mvs_not_ptr
  chunk m bytes (NOTP: chunk <> Mptr) (NOANY: chunk <> Many64) :
  <<EQ: normalize_mvs chunk m bytes = bytes>>.
Proof. unfold normalize_mvs, normalize_check. des_ifs. Qed.

Definition change_check (chunk: memory_chunk) (mvs: list memval) : bool :=
  normalize_check chunk mvs && (negb (forallb is_byte_mv mvs)) && match proj_value qarchi mvs with
                                                                  | Vundef => negb (undef_in_bytes mvs)
                                                                  | _ => false
                                                                  end.

Lemma intptr_normalize_mvs_same_aux
  mv (NPTR: is_intptr_mv mv = true):
  forall m1 m2, _decode_normalize_mv m1 mv = _decode_normalize_mv m2 mv.
Proof. i. destruct mv; ss. des_ifs; ss; clarify. Qed.

Lemma intptr_normalize_mvs_same_aux2
  mvs (NPTR: forallb is_intptr_mv mvs = true):
  forall m1 m2, map (_decode_normalize_mv m1) mvs = map (_decode_normalize_mv m2) mvs.
Proof.
  i. ginduction mvs; ss. i. eapply andb_prop in NPTR. des.
  erewrite (IHmvs _ m1 m2); eauto. erewrite intptr_normalize_mvs_same_aux; eauto.
  Unshelve. eauto.
Qed.

Lemma intptr_normalize_mvs_same
  mvs (NPTR: forallb is_intptr_mv mvs = true):
  forall chunk m1 m2, normalize_mvs chunk m1 mvs = normalize_mvs chunk m2 mvs.
Proof.
  i. unfold normalize_mvs, normalize_check. des_ifs_safe.
  eapply intptr_normalize_mvs_same_aux2; eauto.
Qed.

(* i think not all undef, in undef is also unchange *)
Lemma bytes_all_undef_not_change l chunk
    (LEN: l <> [])
    (UNDEFS: bytes_all_undef l = true):
  Mem.change_check chunk l = false.
Proof.
  destruct chunk; ss.
  - unfold change_check. repeat erewrite andb_false_iff. left. left.
    ss. unfold is_mixed_mvs. destruct Archi.ptr64; ss. erewrite andb_false_iff. left.
    destruct l; ss. eapply andb_prop in UNDEFS. des. ginduction l; ss; i.
    + destruct m; ss.
    + eapply andb_prop in UNDEFS0. des. destruct m; ss.
  - unfold change_check. repeat erewrite andb_false_iff. left. left.
    ss. unfold is_mixed_mvs. destruct Archi.ptr64; ss. erewrite andb_false_iff. left.
    destruct l; ss. eapply andb_prop in UNDEFS. des. ginduction l; ss; i.
    + destruct m; ss.
    + eapply andb_prop in UNDEFS0. des. destruct m; ss.
Qed.

Lemma undef_in_bytes_not_change l chunk
    (LEN: l <> [])
    (UNDEFS: undef_in_bytes l = true):
  Mem.change_check chunk l = false.
Proof.
  destruct chunk; ss.
  - unfold change_check. repeat erewrite andb_false_iff. left. left.
    ss. unfold is_mixed_mvs. destruct Archi.ptr64; ss. erewrite andb_false_iff. left.
    unfold undef_in_bytes in UNDEFS. erewrite existsb_exists in UNDEFS. des.
    erewrite forallb_false_forall. ii. exploit H; eauto. i. destruct x; ss.
  - unfold change_check. repeat erewrite andb_false_iff. left. left.
    ss. unfold is_mixed_mvs. destruct Archi.ptr64; ss. erewrite andb_false_iff. left.
    unfold undef_in_bytes in UNDEFS. erewrite existsb_exists in UNDEFS. des.
    erewrite forallb_false_forall. ii. exploit H; eauto. i. destruct x; ss.
Qed.

Lemma _decode_normalize_mv_byte m b:
  <<EQ: _decode_normalize_mv m (Byte b) = Byte b>>.
Proof. ss. Qed.

Lemma _decode_normalize_mv_byte_map
  m bytes (BYTES: forallb is_byte_mv bytes = true):
  <<EQ: map (_decode_normalize_mv m) bytes = bytes>>.
Proof.
  ginduction bytes; ss; ii. des_ifs. destruct a; ss. r. decEq. eapply IHbytes; eauto.
Qed.

Lemma bytes_mixed bytes (LEN: (Datatypes.length bytes > 0)%nat)
  (BYTES: forallb is_byte_mv bytes = true):
  <<MIXED: is_mixed_mvs bytes = true>>.
Proof.
  unfold is_mixed_mvs. r. rewrite andb_true_iff. split.
  { rewrite forallb_forall in *. ii. eapply BYTES in H. unfold is_ptrlike_mv. destruct x; ss. }
  rewrite negb_true_iff. rewrite forallb_false_forall. ii. rewrite forallb_forall in BYTES.
  destruct bytes; ss; [lia|]. exploit H; eauto. i. exploit BYTES; eauto. i. destruct m; ss.
Qed.

Lemma normalize_mvs_pure
  chunk m bytes (PURE: is_mixed_mvs bytes = false \/ forallb is_byte_mv bytes = true) :
  <<EQ: normalize_mvs chunk m bytes = bytes>>.
Proof.
  destruct bytes; ss.
  { unfold normalize_mvs, normalize_check. ss. des_ifs. }
  unfold normalize_mvs, normalize_check. des.
  { rewrite PURE. des_ifs. }
  exploit (bytes_mixed (m0::bytes)); eauto; [ss; lia|]. i.
  rewrite H. rewrite _decode_normalize_mv_byte_map; eauto. des_ifs.
Qed.

Lemma chunk_normalize_mvs
  chunk m bytes (CHUNK: ~(chunk = Mint64 \/ chunk = Mint32 \/ chunk = Many64 \/ chunk = Many32)):
  <<EQ: normalize_mvs chunk m bytes = bytes>>.
Proof. unfold normalize_mvs. destruct chunk; ss; exfalso; eapply CHUNK; eauto. Qed.

Lemma chunk_normalize_mvs64
  chunk m bytes (SF: Archi.ptr64 = true) (CHUNK: ~(chunk = Mint64 \/ chunk = Many64)):
  <<EQ: normalize_mvs chunk m bytes = bytes>>.
Proof. unfold normalize_mvs. destruct chunk; ss; exfalso; eapply CHUNK; eauto. Qed.

Lemma _normalize_mv_same_concrete m m' byte
    (SAME: mem_concrete m = mem_concrete m'):
  <<EQ: _decode_normalize_mv m byte = _decode_normalize_mv m' byte>>.
Proof.
  unfold _decode_normalize_mv. des_ifs; unfold to_int, ptr2int_v, ptr2int in *; rewrite SAME in Heq; des_ifs.
Qed.

Lemma normalize_mvs_same_concrete m m' chunk bytes
    (SAME: mem_concrete m = mem_concrete m'):
  <<EQ: normalize_mvs chunk m bytes = normalize_mvs chunk m' bytes>>.
Proof.
  unfold normalize_mvs, normalize_check. des_ifs;
    clear Heq; induction bytes; ss; rewrite IHbytes; erewrite _normalize_mv_same_concrete; eauto.
Qed.

Lemma inj_bytes_no_undef bl (INJBYTE: In Undef (inj_bytes bl)): <<FALSE: False>>.
Proof. ginduction bl; ss. ii. des; clarify. eauto. Qed.

Lemma encode_val_pure chunk v:
  <<PURE: (~ In Undef (encode_val chunk v) /\ (is_mixed_mvs_old (encode_val chunk v) = false)) \/ bytes_all_undef (encode_val chunk v) = true>>.
Proof.
  destruct chunk, v; ss; auto; des_ifs; left; split; ss; ii; des; clarify.
  all: try (eapply inj_bytes_no_undef; eauto).
Qed.

Lemma normalize_mvs_undef m chunk mvl:
  <<EQ: exists mvl', normalize_mvs chunk m (Undef :: mvl) = Undef :: mvl' >>.
Proof. unfold normalize_mvs. des_ifs; esplits; eauto; ss. Qed.

Lemma encode_val_change_check_false chunk v:
  change_check chunk (encode_val chunk v) = false.
Proof.
  unfold change_check. destruct chunk; destruct v; ss.
  unfold qarchi. des_ifs_safe. unfold inj_value in Heq0.
  erewrite check_inj_value in Heq0. clarify.
Qed.

(** [load chunk m b ofs] perform a read in memory state [m], at address
  [b] and offset [ofs].  It returns the value of the memory chunk
  at that address.  [None] is returned if the accessed bytes
  are not readable. *)

Definition load (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z): option val :=
  if valid_access_dec m chunk b ofs Readable
  then
    Some (decode_val chunk (normalize_mvs chunk m (getN (size_chunk_nat chunk) ofs (m.(mem_contents)#b))))
  else None.

(** [loadv chunk m addr] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match to_ptr addr m with
  | Some (Vptr b ofs) => load chunk m b (Ptrofs.unsigned ofs)
  | _ => None
  end
.

(** [loadbytes m b ofs n] reads [n] consecutive bytes starting at
  location [(b, ofs)].  Returns [None] if the accessed locations are
  not readable. *)

Definition loadbytes (m: mem) (b: block) (ofs n: Z): option (list memval) :=
  if range_perm_dec m b ofs (ofs + n) Cur Readable
  then Some (getN (Z.to_nat n) ofs (m.(mem_contents)#b))
  else None.

Definition loadbytes_no_perm (m: mem) (b: block) (ofs n: Z): list memval :=
  (getN (Z.to_nat n) ofs (m.(mem_contents)#b)).

(** Memory stores. *)

(** Writing N adjacent bytes in a block content. *)

Fixpoint setN (vl: list memval) (p: Z) (c: ZMap.t memval) {struct vl}: ZMap.t memval :=
  match vl with
  | nil => c
  | v :: vl' => setN vl' (p + 1) (ZMap.set p v c)
  end.

Remark setN_other:
  forall vl c p q,
  (forall r, p <= r < p + Z.of_nat (length vl) -> r <> q) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  induction vl; intros; simpl.
  auto.
  simpl length in H. rewrite Nat2Z.inj_succ in H.
  transitivity (ZMap.get q (ZMap.set p a c)).
  apply IHvl. intros. apply H. lia.
  apply ZMap.gso. apply not_eq_sym. apply H. lia.
Qed.

Remark setN_outside:
  forall vl c p q,
  q < p \/ q >= p + Z.of_nat (length vl) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  intros. apply setN_other.
  intros. lia.
Qed.

Remark getN_setN_same:
  forall vl p c,
  getN (length vl) p (setN vl p c) = vl.
Proof.
  induction vl; intros; simpl.
  auto.
  decEq.
  rewrite setN_outside. apply ZMap.gss. lia.
  apply IHvl.
Qed.

Remark getN_exten:
  forall c1 c2 n p,
  (forall i, p <= i < p + Z.of_nat n -> ZMap.get i c1 = ZMap.get i c2) ->
  getN n p c1 = getN n p c2.
Proof.
  induction n; intros. auto. rewrite Nat2Z.inj_succ in H. simpl. decEq.
  apply H. lia. apply IHn. intros. apply H. lia.
Qed.

Remark getN_setN_disjoint:
  forall vl q c n p,
  Intv.disjoint (p, p + Z.of_nat n) (q, q + Z.of_nat (length vl)) ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_exten. intros. apply setN_other.
  intros; red; intros; subst r. eelim H; eauto.
Qed.

Remark getN_setN_outside:
  forall vl q c n p,
  p + Z.of_nat n <= q \/ q + Z.of_nat (length vl) <= p ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_setN_disjoint. apply Intv.disjoint_range. auto.
Qed.

Remark setN_default:
  forall vl q c, fst (setN vl q c) = fst c.
Proof.
  induction vl; simpl; intros. auto. rewrite IHvl. auto.
Qed.

(** [store chunk m b ofs v] perform a write in memory state [m].
  Value [v] is stored at address [b] and offset [ofs].
  Return the updated memory store, or [None] if the accessed bytes
  are not writable. *)

Program Definition store (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val): option mem :=
  if valid_access_dec m chunk b ofs Writable then
    Some (mkmem (PMap.set b
                          (setN (encode_val chunk v) ofs (m.(mem_contents)#b))
                          m.(mem_contents))
                m.(mem_access)
                m.(mem_concrete)
                m.(nextblock)
                _ _ _ _ _ _ _ _ )
  else
    None.
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Qed.
Next Obligation.
  apply m.(nextblocks_logical). exact H0.
Qed.
Next Obligation.
  eapply m.(valid_address_bounded).
  inversion IN_BLOCK.
  econs.
  exact CONCRETE.  exact PERM. eauto.
Qed.
Next Obligation.
  unfold uniqueness in *. intros b1 b2 B1 B2.
  apply access_le_no_overlap with (acc2:=m.(mem_access)) (acc1:=m.(mem_access)) (addr:=addr) (concrete:=m.(mem_concrete)).
  - unfold access_le. intros. exact M2_NONE.
  - apply m.(no_concrete_overlap).
  - exact B1. - exact B2.
Qed.
Next Obligation.
  eapply concrete_align; eauto.
Qed.
Next Obligation.
  eapply weak_valid_address_range; eauto.
Qed.

(** [storev chunk m addr v] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v
  | Vint n => if negb Archi.ptr64 then 
               (match denormalize (Int.unsigned n) m with
                | Some (b, ofs) => store chunk m b ofs v
                | _ => None
                end)
             else None
  | Vlong n => if Archi.ptr64 then 
                (match denormalize (Int64.unsigned n) m with
                 | Some (b, ofs) => store chunk m b ofs v
                 | _ => None
                 end)
              else None
  | _ => None
  end.

(** [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)

Program Definition storebytes (m: mem) (b: block) (ofs: Z) (bytes: list memval) : option mem :=
  if range_perm_dec m b ofs (ofs + Z.of_nat (length bytes)) Cur Writable then
    Some (mkmem
             (PMap.set b (setN bytes ofs (m.(mem_contents)#b)) m.(mem_contents))
             m.(mem_access)
             m.(mem_concrete)
             m.(nextblock)
             _ _ _ _ _ _ _ _)
  else
    None.
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Qed.
Next Obligation.
  apply m.(nextblocks_logical). exact H0.
Qed.
Next Obligation.
  eapply m.(valid_address_bounded).
  inversion IN_BLOCK.
  econs; eauto.
Qed.
Next Obligation.
  unfold uniqueness in *. intros b1 b2 B1 B2.
  apply access_le_no_overlap with (acc2:=m.(mem_access)) (acc1:=m.(mem_access)) (addr:=addr) (concrete:=m.(mem_concrete)).
  - unfold access_le. intros. exact M2_NONE.
  - apply m.(no_concrete_overlap).
  - exact B1. - exact B2.
Qed.
Next Obligation.
  eapply concrete_align; eauto.
Qed.
Next Obligation.
  eapply weak_valid_address_range; eauto.
Qed.

Program Definition storebytes_no_perm (m: mem) (b: block) (ofs: Z) (bytes: list memval) : mem :=
  (mkmem
     (PMap.set b (setN bytes ofs (m.(mem_contents)#b)) m.(mem_contents))
     m.(mem_access)
     m.(mem_concrete)
     m.(nextblock)
     _ _ _ _ _ _ _ _).
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Qed.
Next Obligation.
  apply m.(nextblocks_logical). exact H.
Qed.
Next Obligation.
  eapply m.(valid_address_bounded).
  inversion IN_BLOCK.
  econs; eauto.
Qed.
Next Obligation.
  unfold uniqueness in *. intros b1 b2 B1 B2.
  apply access_le_no_overlap with (acc2:=m.(mem_access)) (acc1:=m.(mem_access)) (addr:=addr) (concrete:=m.(mem_concrete)).
  - unfold access_le. intros. exact M2_NONE.
  - apply m.(no_concrete_overlap).
  - exact B1.
  - exact B2.
Qed.
Next Obligation.
  eapply concrete_align; eauto.
Qed.
Next Obligation.
  eapply weak_valid_address_range; eauto.
Qed.

(** [drop_perm m b lo hi p] sets the max permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have current permissions
    [Freeable] in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

Program Definition drop_perm (m: mem) (b: block) (lo hi: Z) (p: permission): option mem :=
  if range_perm_dec m b lo hi Cur Freeable then
    Some (mkmem m.(mem_contents)
                (PMap.set b
                        (fun ofs k => if zle lo ofs && zlt ofs hi then Some p else m.(mem_access)#b ofs k)
                        m.(mem_access))
                m.(mem_concrete)
                m.(nextblock)
                _ _ _ _ _ _ _ _)
  else None.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  destruct (zle lo ofs && zlt ofs hi). red; auto with mem. apply access_max.
  apply access_max.
Qed.
Next Obligation.
  specialize (nextblock_noaccess m b0 ofs k H0). intros.
  rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  destruct (zle lo ofs). destruct (zlt ofs hi).
  assert (perm m b ofs k Freeable). apply perm_cur. apply H; auto.
  unfold perm in H2. rewrite H1 in H2. contradiction.
  auto. auto. auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  apply m.(nextblocks_logical). exact H0.
Qed.
Next Obligation.
  eapply m.(valid_address_bounded).
  inversion IN_BLOCK.
  econs; eauto.
  destruct (Pos.eq_dec bo b).
  - rewrite e in *. rewrite PMap.gss in PERM.
    destruct PERM as [perm PERM].
    unfold range_perm in H. specialize H with (addr-caddr).
    assert (zle lo (addr - caddr) && zlt (addr - caddr) hi = true -> lo <= addr - caddr < hi).
    {  intros. split.
      destruct zle in H0. exact l. inversion H0.
      destruct zlt in H0. exact l. inversion H0. apply andb_true_iff in H2. destruct H2. inversion H2. }
    simpl in PERM. destruct (zle lo (addr - caddr) && zlt (addr - caddr) hi).
    + assert (Mem.perm m b (addr - caddr) Cur Freeable).
      apply H. apply H0. reflexivity.
      exists Freeable. unfold Mem.perm in H1. unfold perm_order' in H1. simpl.
      induction  ((mem_access m) # b (addr - caddr) Cur); inv H1.
      { exploit H; eauto. i. eapply perm_cur_max in H1.
        unfold Mem.perm, perm_order' in *. des_ifs; inv H1; eauto. }
      { exploit H; eauto. i. eapply perm_cur_max in H1.
        unfold Mem.perm, perm_order' in *. des_ifs; inv H1; eauto. }
    + exists perm. exact PERM.
  - rewrite PMap.gso in PERM. exact PERM. exact n.
Qed.
Next Obligation.
  unfold uniqueness in *. intros b1 b2 B1 B2.
  apply access_le_no_overlap with (acc2:=m.(mem_access)) (acc1:=(PMap.set b (fun (ofs : Z) (k : perm_kind) => if zle lo ofs && zlt ofs hi then Some p else (mem_access m)# b ofs k) m.(mem_access))) (addr:=addr) (concrete:=m.(mem_concrete)).
  - unfold access_le. intros.
    destruct (Pos.eq_dec b0 b).
    + rewrite e in *. rewrite PMap.gss.
      unfold range_perm in H. specialize H with off.
      assert (zle lo off && zlt off hi = true -> lo <= off < hi).
      { intros. split.
      destruct zle in H0. exact l. inversion H0.
      destruct zlt in H0. exact l. inversion H0. apply andb_true_iff in H2. destruct H2. inversion H2. }
      destruct(zle lo off && zlt off hi).
      * assert (lo <= off <hi).
        { apply H0. reflexivity. }
        apply H in H1. unfold perm, perm_order' in H1. des_ifs.
        assert (perm m b off Cur Freeable).
        { unfold perm, perm_order'. rewrite Heq. ss. }
        eapply perm_cur_max in H2. unfold perm, perm_order' in H2. des_ifs.
      * exact M2_NONE.
    + rewrite PMap.gso; try exact n; try exact M2_NONE.
  - apply m.(no_concrete_overlap).
  - exact B1. - exact B2.
Qed.
Next Obligation.
  eapply concrete_align; eauto. ii.
  exploit RPERM; eauto. ii. des.
  destruct (peq b b0); subst.
  - rewrite PMap.gss in H1. des_ifs; eauto.
    assert (lo <= o < hi).
    { i; split.
      destruct zle in Heq. exact l. inversion Heq.
      destruct zlt in Heq. exact l. inversion Heq.
      apply andb_true_iff in H4. des; clarify. }
    eapply H in H3. eapply perm_cur_max in H3.
    eapply perm_implies; eauto. eapply perm_any_N.
  - rewrite PMap.gso in H1; eauto.
Qed.
Next Obligation.
  unfold _weak_valid_pointer, _valid_pointer in WVLD.
  destruct (peq b b0); subst.
  2: { rewrite PMap.gso in WVLD; eauto.
       eapply weak_valid_address_range; eauto. }
  eapply weak_valid_address_range; eauto.
  rewrite PMap.gss in WVLD; eauto.
  unfold _weak_valid_pointer, _valid_pointer.
  des_ifs.
  - unfold range_perm in H. specialize (H ofs). unfold perm in H.
    left. exploit H; eauto. eapply andb_prop in Heq. inv Heq.
    destruct zle in H2; inv H2. destruct zlt in H3; inv H3.
    eauto. ii. eapply perm_cur_max. eapply perm_implies; eauto. eapply perm_any_N.
  - unfold range_perm in H. specialize (H ofs). unfold perm in H.
    left. exploit H; eauto. eapply andb_prop in Heq. inv Heq.
    destruct zle in H2; inv H2. destruct zlt in H3; inv H3.
    eauto. ii.  eapply perm_cur_max. eapply perm_implies; eauto. eapply perm_any_N.
  - unfold range_perm in H. specialize (H (ofs - 1)). unfold perm in H.
    right. exploit H; eauto. eapply andb_prop in Heq0. inv Heq0.
    destruct zle in H2; inv H2. destruct zlt in H3; inv H3.
    eauto. ii. eapply perm_cur_max. eapply perm_implies; eauto. eapply perm_any_N.
Qed.

(** * Properties of the memory operations *)

(** Properties of the empty store. *)

Theorem nextblock_empty: nextblock empty = 1%positive.
Proof. reflexivity. Qed.

Theorem perm_empty: forall b ofs k p, ~perm empty b ofs k p.
Proof.
  intros. unfold perm, empty; simpl. rewrite PMap.gi. simpl. tauto.
Qed.

Theorem valid_access_empty: forall chunk b ofs p, ~valid_access empty chunk b ofs p.
Proof.
  intros. red; intros. elim (perm_empty b ofs Cur p). apply H.
  generalize (size_chunk_pos chunk); lia.
Qed.

(** ** Properties related to [load] *)

Theorem valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v.
Proof.
  intros. econstructor. unfold load. rewrite pred_dec_true; eauto.
Qed.

Theorem load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable.
Proof.
  intros until v. unfold load.
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  auto.
  congruence.
Qed.

Lemma load_result:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  v = decode_val chunk (normalize_mvs chunk m (getN (size_chunk_nat chunk) ofs (m.(mem_contents)#b))).
Proof.
  intros until v. unfold load.
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  congruence.
  congruence.
Qed.

Local Hint Resolve load_valid_access valid_access_load: mem.

Theorem load_type:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_type v (type_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros. rewrite H0.
  apply decode_val_type.
Qed.

Theorem load_rettype:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_rettype v (rettype_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros. rewrite H0.
  apply decode_val_rettype.
Qed.

Theorem load_cast:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end.
Proof.
  intros. exploit load_result; eauto.
  set (l := getN (size_chunk_nat chunk) ofs m.(mem_contents)#b).
  intros. subst v. apply decode_val_cast.
Qed.

Theorem load_int8_signed_unsigned:
  forall m b ofs,
  load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint8signed) with (size_chunk_nat Mint8unsigned).
  set (cl := (getN (size_chunk_nat Mint8unsigned) ofs m.(mem_contents)#b)).
  unfold normalize_mvs. des_ifs_safe.
  destruct (valid_access_dec m Mint8signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_false; auto.
Qed.

Theorem load_int16_signed_unsigned:
  forall m b ofs,
  load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs).
Proof.
  intros. unfold load.
  repeat (rewrite chunk_normalize_mvs; eauto); try by (ii; des; clarify).
  change (size_chunk_nat Mint16signed) with (size_chunk_nat Mint16unsigned).
  set (cl := getN (size_chunk_nat Mint16unsigned) ofs m.(mem_contents)#b).
  destruct (valid_access_dec m Mint16signed b ofs Readable).
  simpl.
  rewrite pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_false; auto.
Qed.

(** ** Properties related to [loadbytes] *)

Theorem range_perm_loadbytes:
  forall m b ofs len,
  range_perm m b ofs (ofs + len) Cur Readable ->
  exists bytes, loadbytes m b ofs len = Some bytes.
Proof.
  intros. econstructor. unfold loadbytes. rewrite pred_dec_true; eauto.
Qed.

Theorem loadbytes_range_perm:
  forall m b ofs len bytes,
  loadbytes m b ofs len = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable.
Proof.
  intros until bytes. unfold loadbytes.
  destruct (range_perm_dec m b ofs (ofs + len) Cur Readable). auto. congruence.
Qed.

Theorem loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some(decode_val chunk (normalize_mvs chunk m bytes)).
Proof.
  unfold loadbytes, load; intros.
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur Readable);
  try congruence.
  inv H. rewrite pred_dec_true. auto.
  split; auto.
Qed.

Theorem load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk (normalize_mvs chunk m bytes).
Proof.
  intros. exploit load_valid_access; eauto. intros [A B].
  exploit load_result; eauto. intros.
  exists (getN (size_chunk_nat chunk) ofs m.(mem_contents)#b); split.
  unfold loadbytes. rewrite pred_dec_true; auto.
  auto.
Qed.

Lemma getN_length:
  forall c n p, length (getN n p c) = n.
Proof.
  induction n; simpl; intros. auto. decEq; auto.
Qed.

Theorem loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = Z.to_nat n.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable); try congruence.
  inv H. apply getN_length.
Qed.

Theorem loadbytes_empty:
  forall m b ofs n,
  n <= 0 -> loadbytes m b ofs n = Some nil.
Proof.
  intros. unfold loadbytes. rewrite pred_dec_true. rewrite Z_to_nat_neg; auto.
  red; intros. extlia.
Qed.

Lemma getN_concat:
  forall c n1 n2 p,
  getN (n1 + n2)%nat p c = getN n1 p c ++ getN n2 (p + Z.of_nat n1) c.
Proof.
  induction n1; intros.
  simpl. decEq. lia.
  rewrite Nat2Z.inj_succ. simpl. decEq.
  replace (p + Z.succ (Z.of_nat n1)) with ((p + 1) + Z.of_nat n1) by lia.
  auto.
Qed.

Theorem loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2).
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n1) Cur Readable); try congruence.
  destruct (range_perm_dec m b (ofs + n1) (ofs + n1 + n2) Cur Readable); try congruence.
  rewrite pred_dec_true. rewrite Z2Nat.inj_add by lia.
  rewrite getN_concat. rewrite Z2Nat.id by lia.
  congruence.
  red; intros.
  assert (ofs0 < ofs + n1 \/ ofs0 >= ofs + n1) by lia.
  destruct H4. apply r; lia. apply r0; lia.
Qed.

Theorem loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + (n1 + n2)) Cur Readable);
  try congruence.
  rewrite Z2Nat.inj_add in H by lia. rewrite getN_concat in H.
  rewrite Z2Nat.id in H by lia.
  repeat rewrite pred_dec_true.
  econstructor; econstructor.
  split. reflexivity. split. reflexivity. congruence.
  red; intros; apply r; lia.
  red; intros; apply r; lia.
Qed.

(* not true. if concrete memory is same, it will be true *)
(* Theorem load_rep: *)
(*  forall ch m1 m2 b ofs v1 v2, *)
(*   (forall z, 0 <= z < size_chunk ch -> ZMap.get (ofs + z) m1.(mem_contents)#b = ZMap.get (ofs + z) m2.(mem_contents)#b) -> *)
(*   load ch m1 b ofs = Some v1 -> *)
(*   load ch m2 b ofs = Some v2 -> *)
(*   v1 = v2. *)
(* Proof. *)
(*   intros. *)
(*   apply load_result in H0. *)
(*   apply load_result in H1. *)
(*   subst. *)
(*   f_equal. *)
(*   rewrite size_chunk_conv in H. *)
(*   remember (size_chunk_nat ch) as n; clear Heqn. *)
(*   revert ofs H; induction n; intros; simpl; auto. *)
(*   f_equal. *)
(*   rewrite Nat2Z.inj_succ in H. *)
(*   replace ofs with (ofs+0) by lia. *)
(*   apply H; lia. *)
(*   apply IHn. *)
(*   intros. *)
(*   rewrite <- Z.add_assoc. *)
(*   apply H. *)
(*   rewrite Nat2Z.inj_succ. lia. *)
(* Qed. *)

Theorem load_int64_split:
  forall m b ofs v,
  load Mint64 m b ofs = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     load Mint32 m b ofs = Some (if Archi.big_endian then v1 else v2)
  /\ load Mint32 m b (ofs + 4) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).
Proof.
  intros.
  exploit load_valid_access; eauto. intros [A B]. simpl in *.
  exploit load_loadbytes. eexact H. simpl. intros [bytes [LB EQ]].
  change 8 with (4 + 4) in LB.
  exploit loadbytes_split. eexact LB. lia. lia.
  intros (bytes1 & bytes2 & LB1 & LB2 & APP).
  change 4 with (size_chunk Mint32) in LB1.
  exploit loadbytes_load. eexact LB1.
  simpl. apply Z.divide_trans with 8; auto. exists 2; auto.
  intros L1.
  change 4 with (size_chunk Mint32) in LB2.
  exploit loadbytes_load. eexact LB2.
  simpl. apply Z.divide_add_r. apply Z.divide_trans with 8; auto. exists 2; auto. exists 1; auto.
  intros L2.
  exists (decode_val Mint32 (if Archi.big_endian then (normalize_mvs Mint32 m bytes1) else (normalize_mvs Mint32 m bytes2)));
  exists (decode_val Mint32 (if Archi.big_endian then (normalize_mvs Mint32 m bytes2) else (normalize_mvs Mint32 m bytes1))).
  split. destruct Archi.big_endian; auto.
  split. destruct Archi.big_endian; auto.
  rewrite EQ. rewrite APP. ss.
Qed.

Lemma addressing_int64_split:
  forall i,
  Archi.ptr64 = false ->
  (8 | Ptrofs.unsigned i) ->
  Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr 4))) = Ptrofs.unsigned i + 4.
Proof.
  intros.
  rewrite Ptrofs.add_unsigned.
  replace (Ptrofs.unsigned (Ptrofs.of_int (Int.repr 4))) with (Int.unsigned (Int.repr 4))
    by (symmetry; apply Ptrofs.agree32_of_int; auto).
  change (Int.unsigned (Int.repr 4)) with 4.
  apply Ptrofs.unsigned_repr.
  exploit (Zdivide_interval (Ptrofs.unsigned i) Ptrofs.modulus 8).
  lia. apply Ptrofs.unsigned_range. auto.
  exists (two_p (Ptrofs.zwordsize - 3)).
  unfold Ptrofs.modulus, Ptrofs.zwordsize, Ptrofs.wordsize.
  unfold Wordsize_Ptrofs.wordsize. destruct Archi.ptr64; reflexivity.
  unfold Ptrofs.max_unsigned. lia.
Qed.

Theorem loadv_int64_split:
  forall m a v,
  loadv Mint64 m a = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     loadv Mint32 m a = Some (if Archi.big_endian then v1 else v2)
  /\ loadv Mint32 m (Val.add a (Vint (Int.repr 4))) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).
Proof.
  intros. destruct a; simpl in H; inv H.
  { unfold loadv, to_ptr in H2. rewrite H0 in H2. clarify. }
  unfold loadv in H2. simpl in H2.
  exploit load_int64_split; eauto. intros (v1 & v2 & L1 & L2 & EQ).
  unfold Val.add; rewrite H0.
  assert (NV: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr 4))) = Ptrofs.unsigned i + 4).
  { apply addressing_int64_split; auto.
    exploit load_valid_access. eexact H2. intros [P Q]. auto. }
  exists v1, v2.
Opaque Ptrofs.repr.
  unfold loadv. simpl.
  split. auto.
  split. simpl. rewrite NV. auto.
  auto.
Qed.

(** ** Properties related to [store] *)

Theorem valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
Proof.
  intros.
  unfold store.
  destruct (valid_access_dec m1 chunk b ofs Writable).
  eauto.
  contradiction.
Defined.

Local Hint Resolve valid_access_store: mem.

Section NALLOC.

Variable lo hi: Z.
Variable b: block.
Variable m m': mem.
Hypothesis NA: nonempty_alloc m b lo hi = Some m'.

Lemma nonempty_alloc_concrete:
  m.(mem_concrete) = m'.(mem_concrete).
Proof.  
  destruct (perm_dec m b lo Max Nonempty).
  2:{ unfold Mem.nonempty_alloc in NA. des_ifs. }
  destruct (is_concrete m b) eqn:CONC.
  { unfold Mem.nonempty_alloc in NA. des_ifs. }
  unfold Mem.nonempty_alloc in NA. des_ifs.
Qed.

Lemma nonempty_alloc_nextblock:
  m.(nextblock) = m'.(nextblock).
Proof.
  destruct (perm_dec m b lo Max Nonempty).
  2:{ unfold Mem.nonempty_alloc in NA. des_ifs. }
  destruct (is_concrete m b) eqn:CONC.
  { unfold Mem.nonempty_alloc in NA. des_ifs. }
  unfold Mem.nonempty_alloc in NA. des_ifs.
Qed.

End NALLOC.

Section STORE.
Variable chunk: memory_chunk.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable v: val.
Variable m2: mem.
Hypothesis STORE: store chunk m1 b ofs v = Some m2.

Lemma store_access: mem_access m2 = mem_access m1.
Proof.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Lemma store_mem_contents:
  mem_contents m2 = PMap.set b (setN (encode_val chunk v) ofs m1.(mem_contents)#b) m1.(mem_contents).
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem perm_store_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Proof.
  intros.
 unfold perm in *. rewrite store_access; auto.
Qed.

Theorem perm_store_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Proof.
  intros. unfold perm in *.  rewrite store_access in H; auto.
Qed.

Local Hint Resolve perm_store_1 perm_store_2: mem.

Theorem nextblock_store:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem concrete_store:
  m1.(mem_concrete) = m2.(mem_concrete).
Proof.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE. reflexivity.
Qed.

Theorem store_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store; auto.
Qed.

Theorem store_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store in H; auto.
Qed.

Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.

Theorem store_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem store_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem store_valid_access_3:
  valid_access m1 chunk b ofs Writable.
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable).
  auto.
  congruence.
Qed.

Local Hint Resolve store_valid_access_1 store_valid_access_2 store_valid_access_3: mem.

Lemma store_pure_memval
    bytes (LB: loadbytes m2 b ofs (size_chunk chunk) = Some bytes):
  <<PURE:((~ In Undef bytes) /\ (is_mixed_mvs_old bytes = false)) \/ bytes_all_undef bytes = true>>.
Proof.
  unfold loadbytes in LB. des_ifs. rewrite store_mem_contents. ss.
  replace (Z.to_nat (size_chunk chunk)) with (size_chunk_nat chunk) by ss.
  replace (size_chunk_nat chunk) with (length (encode_val chunk v)).
  2:{ rewrite encode_val_length. repeat rewrite size_chunk_conv in H. apply Nat2Z.inj; auto. }
  rewrite PMap.gss. rewrite getN_setN_same. eapply encode_val_pure.
Qed.

Lemma store_pure_memval_check
    bytes (LB: loadbytes m2 b ofs (size_chunk chunk) = Some bytes):
  <<PURE: change_check chunk bytes = false>>.
Proof.
  unfold loadbytes in LB. des_ifs. rewrite store_mem_contents. ss.
  replace (Z.to_nat (size_chunk chunk)) with (size_chunk_nat chunk) by ss.
  replace (size_chunk_nat chunk) with (length (encode_val chunk v)).
  2:{ rewrite encode_val_length. repeat rewrite size_chunk_conv in H. apply Nat2Z.inj; auto. }
  rewrite PMap.gss. rewrite getN_setN_same. eapply encode_val_change_check_false.
Qed.

Lemma store_loadbytes_same
    bytes (LB: loadbytes m2 b ofs (size_chunk chunk) = Some bytes):
  <<EQ: encode_val chunk v = bytes>>.
Proof.
  unfold loadbytes in LB. des_ifs. rewrite store_mem_contents.
  replace (Z.to_nat (size_chunk chunk)) with (size_chunk_nat chunk) by ss.
  replace (size_chunk_nat chunk) with (length (encode_val chunk v)).
  2:{ rewrite encode_val_length. repeat rewrite size_chunk_conv in H. apply Nat2Z.inj; auto. }
  rewrite PMap.gss. rewrite getN_setN_same. auto.
Qed.

Theorem load_store_similar:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v'.
Proof.
  intros.
  exploit (valid_access_load m2 chunk').
    eapply valid_access_compat. symmetry; eauto. auto. eauto with mem.
  intros [v' LOAD].
  exists v'; split; auto.
  exploit load_result; eauto. intros B.
  rewrite B. rewrite store_mem_contents; simpl.
  rewrite PMap.gss.
  replace (size_chunk_nat chunk') with (length (encode_val chunk v)).
  rewrite getN_setN_same.
  exploit load_loadbytes; eauto. i. des.
  exploit store_pure_memval.
  { rewrite <- H. eapply H1. }
  i. des.
  (* all undef *)
  2: { rewrite H in H1. erewrite store_loadbytes_same; eauto.
       assert (is_mixed_mvs bytes = false).
       { clear - H3. induction bytes; ss. eapply andb_prop in H3. des.
         destruct a; ss. }
       unfold normalize_mvs, normalize_check. rewrite H4. 
       exploit store_loadbytes_same; eauto. i. des. subst. des_ifs;
         apply decode_encode_val_general. }
  unfold is_mixed_mvs_old in H4. rewrite andb_false_iff in H4. des.
  rewrite normalize_mvs_pure.
  2:{ do 2 rewrite andb_false_iff in H4. rewrite negb_false_iff in H4.
      erewrite (store_loadbytes_same bytes); eauto.
      { rewrite negb_false_iff in H4. des; auto; left; unfold is_mixed_mvs; rewrite H4; ss.
        rewrite andb_false_r. ss. }
      rewrite <- H. eauto. }
  apply decode_encode_val_general.
  { rewrite negb_false_iff in H4.
    assert (MIXED: is_mixed_mvs (encode_val chunk v) = true).
    { unfold is_mixed_mvs.
      assert (LEN: (Datatypes.length bytes > 0)%nat).
      { erewrite loadbytes_length; eauto. destruct chunk'; ss; lia. }
      exploit store_loadbytes_same; eauto.
      { rewrite <- H. eauto. }
      i. rewrite H5. repeat rewrite andb_true_iff. splits.
      - rewrite forallb_forall in *. ii. eapply H4 in H6.
        unfold is_ptrlike_mv. rewrite H6. ss.
      - rewrite negb_true_iff. erewrite forallb_false_forall. ii.
        rewrite forallb_forall in H4. destruct bytes; ss; [lia|].
        specialize (H4 m). specialize (H6 m).
        exploit H4; eauto. i. exploit H6; eauto. i.
        clear - H7 H8. destruct m; ss. des_ifs. }
    assert (chunk = Many64 \/ chunk = Many32).
    { destruct Archi.ptr64 eqn:SF.
      - unfold is_intptr_mv in H4. des_ifs_safe. ss.
        erewrite H in H1. exploit store_loadbytes_same; eauto. i. des. subst.
        destruct v; ss; clear - H4; try by des_ifs.
        rewrite forallb_forall in H4. des_ifs; ss; try by (exploit H4; eauto; i; des_ifs).
        assert (exists x, In x (inj_bytes (encode_int 8 (Int64.unsigned i)))).
        { clear. remember (inj_bytes (encode_int 8 (Int64.unsigned i))).
          specialize (length_inj_bytes (encode_int 8 (Int64.unsigned i))).
          i. erewrite encode_int_length in H. rewrite <- Heql in H. clear Heql. destruct l; ss. eauto. }
        des. exploit H4; eauto. i. des_ifs. exfalso. eapply inj_bytes_no_fragment'; eauto.
      - ss. }
    des.
    2:{ unfold normalize_mvs, normalize_check. subst.
        destruct chunk'; ss; des_ifs; apply decode_encode_val_general. }
    subst. ss. destruct chunk'; ss.
    { erewrite chunk_normalize_mvs; eauto. 2:{ ii. des; clarify. } apply decode_encode_val_general. }
    destruct v; ss. unfold decode_val. ss.
    assert (exists bl, proj_bytes (normalize_mvs Many64 m2 (inj_value Q64 (Vlong i))) = Some bl).
    { (* make lemma *)
      unfold normalize_mvs, normalize_check. rewrite MIXED. simpl. unfold rev_if_be_mv. des_ifs.
      destruct l0; ss. des_ifs. esplits; eauto. }
    des. rewrite H5. f_equal. unfold normalize_mvs, normalize_check in H5. simpl in H5. des_ifs.
    assert (l0 = nil) by (destruct l0; ss).
    subst. unfold rev_if_be_mv in Heq8. des_ifs.
    assert (rev (rev (inj_bytes (encode_int 8 (Int64.unsigned i)))) = rev [m8; m7; m6; m5; m4; m3; m0; m]).
    { rewrite <- Heq8. ss. }
    clear Heq8. simpl in H6. rewrite rev_involutive in H6. rewrite <- H6 in H5.
    rewrite proj_inj_bytes in H5. clarify. eapply decode_encode_int_8. }
  rewrite encode_val_length. repeat rewrite size_chunk_conv in H.
  apply Nat2Z.inj; auto.
Qed.

Theorem load_store_similar_2:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  type_of_chunk chunk' = type_of_chunk chunk ->
  load chunk' m2 b ofs = Some (Val.load_result chunk' v).
Proof.
  intros. destruct (load_store_similar chunk') as [v' [A B]]; auto.
  rewrite A. decEq. eapply decode_encode_val_similar with (chunk1 := chunk); eauto.
Qed.

Theorem load_store_same:
  load chunk m2 b ofs = Some (Val.load_result chunk v).
Proof.
  apply load_store_similar_2; auto. lia.
Qed.

Theorem load_store_other:
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m1 chunk' b' ofs' Readable).
  rewrite pred_dec_true.
  decEq. decEq.
  replace (getN (size_chunk_nat chunk') ofs' (mem_contents m1) # b') with (getN (size_chunk_nat chunk') ofs' (mem_contents m2) # b'); cycle 1.
  rewrite store_mem_contents; simpl.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  apply getN_setN_outside. rewrite encode_val_length. repeat rewrite <- size_chunk_conv.
  intuition.
  auto.
  symmetry.
  erewrite normalize_mvs_same_concrete; try eapply concrete_store. eauto.
  eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

Theorem loadbytes_store_same:
  loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v).
Proof.
  intros.
  assert (valid_access m2 chunk b ofs Readable) by eauto with mem.
  unfold loadbytes. rewrite pred_dec_true. rewrite store_mem_contents; simpl.
  rewrite PMap.gss.
  replace (Z.to_nat (size_chunk chunk)) with (length (encode_val chunk v)).
  rewrite getN_setN_same. auto.
  rewrite encode_val_length. auto.
  apply H.
Qed.

Theorem loadbytes_store_other:
  forall b' ofs' n,
  b' <> b
  \/ n <= 0
  \/ ofs' + n <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs' (ofs' + n) Cur Readable).
  rewrite pred_dec_true.
  decEq. rewrite store_mem_contents; simpl.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  destruct H. congruence.
  destruct (zle n 0) as [z | n0].
  rewrite (Z_to_nat_neg _ z). auto.
  destruct H. extlia.
  apply getN_setN_outside. rewrite encode_val_length. rewrite <- size_chunk_conv.
  rewrite Z2Nat.id. auto. lia.
  auto.
  red; intros. eauto with mem.
  rewrite pred_dec_false. auto.
  red; intro; elim n0; red; intros; eauto with mem.
Qed.

Lemma setN_in:
  forall vl p q c,
  p <= q < p + Z.of_nat (length vl) ->
  In (ZMap.get q (setN vl p c)) vl.
Proof.
  induction vl; intros.
  simpl in H. extlia.
  simpl length in H. rewrite Nat2Z.inj_succ in H. simpl.
  destruct (zeq p q). subst q. rewrite setN_outside. rewrite ZMap.gss.
  auto with coqlib. lia.
  right. apply IHvl. lia.
Qed.

Lemma getN_in:
  forall c q n p,
  p <= q < p + Z.of_nat n ->
  In (ZMap.get q c) (getN n p c).
Proof.
  induction n; intros.
  simpl in H; extlia.
  rewrite Nat2Z.inj_succ in H. simpl. destruct (zeq p q).
  subst q. auto.
  right. apply IHn. lia.
Qed.

End STORE.

Local Hint Resolve perm_store_1 perm_store_2: mem.
Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.
Local Hint Resolve store_valid_access_1 store_valid_access_2
             store_valid_access_3: mem.

Lemma load_store_overlap:
  forall chunk m1 b ofs v m2 chunk' ofs' v',
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b ofs' = Some v' ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  exists mv1 mvl mv1' mvl',
      shape_encoding chunk v (mv1 :: mvl)
  /\  shape_decoding chunk' (normalize_mvs chunk' m2 (mv1' :: mvl')) v'
  /\  (   (ofs' = ofs /\ mv1' = mv1)
       \/ (ofs' > ofs /\ In mv1' mvl)
       \/ (ofs' < ofs /\ In mv1 mvl')).
Proof.
  intros.
  exploit load_result; eauto. erewrite store_mem_contents by eauto; simpl.
  rewrite PMap.gss.
  set (c := (mem_contents m1)#b). intros V'.
  destruct (size_chunk_nat_pos chunk) as [sz SIZE].
  destruct (size_chunk_nat_pos chunk') as [sz' SIZE'].
  destruct (encode_val chunk v) as [ | mv1 mvl] eqn:ENC.
  generalize (encode_val_length chunk v); rewrite ENC; simpl; congruence.
  set (c' := setN (mv1::mvl) ofs c) in *.
  exists mv1, mvl, (ZMap.get ofs' c'), (getN sz' (ofs' + 1) c').
  split. rewrite <- ENC. apply encode_val_shape.
  split. rewrite V', SIZE'. ss.
  remember (normalize_mvs chunk' m2 (ZMap.get ofs' c' :: getN sz' (ofs' + 1) c')) as ml.
  destruct ml.
  { clear - Heqml. unfold normalize_mvs in Heqml. des_ifs; ss; des_ifs. }
  apply decode_val_shape.

  destruct (zeq ofs' ofs).
- subst ofs'. left; split. auto. unfold c'. simpl.
  rewrite setN_outside by lia. apply ZMap.gss.
- right. destruct (zlt ofs ofs').
(* If ofs < ofs':  the load reads (at ofs') a continuation byte from the write. *)
(*        ofs   ofs'   ofs+|chunk| *)
(*         [-------------------]       write *)
(*              [-------------------]  read *)
(* *)
+ left; split. lia. unfold c'. simpl. apply setN_in.
  assert (Z.of_nat (length (mv1 :: mvl)) = size_chunk chunk).
  { rewrite <- ENC; rewrite encode_val_length. rewrite size_chunk_conv; auto. }
  simpl length in H3. rewrite Nat2Z.inj_succ in H3. lia.
(* If ofs > ofs':  the load reads (at ofs) the first byte from the write. *)
(*        ofs'   ofs   ofs'+|chunk'| *)
(*                [-------------------]  write *)
(*          [----------------]           read *)
(* *)
+ right; split. lia. replace mv1 with (ZMap.get ofs c').
  apply getN_in.
  assert (size_chunk chunk' = Z.succ (Z.of_nat sz')).
  { rewrite size_chunk_conv. rewrite SIZE'. rewrite Nat2Z.inj_succ; auto. }
  lia.
  unfold c'. simpl. rewrite setN_outside by lia. apply ZMap.gss.
Qed.

Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | (Mint32 | Many32), (Mint32 | Many32) => True
  | (Mint64 | Many64), (Mint64 | Many64) => True
  | _, _ => False
  end.

Lemma compat_pointer_chunks_true:
  forall chunk1 chunk2,
  (chunk1 = Mint32 \/ chunk1 = Many32 \/ chunk1 = Mint64 \/ chunk1 = Many64) ->
  (chunk2 = Mint32 \/ chunk2 = Many32 \/ chunk2 = Mint64 \/ chunk2 = Many64) ->
  quantity_chunk chunk1 = quantity_chunk chunk2 ->
  compat_pointer_chunks chunk1 chunk2.
Proof.
  intros. destruct H as [P|[P|[P|P]]]; destruct H0 as [Q|[Q|[Q|Q]]];
  subst; red; auto; discriminate.
Qed.

Lemma proj_fragment_same bytes bytes' (FRAG: proj_fragment bytes = Some bytes'):
  <<FRAG: bytes = bytes' >>.
Proof.
  ginduction bytes; ii; ss; clarify. des_ifs. r. decEq. eapply IHbytes; eauto.
Qed.

Lemma shape_decoding_pointer_all_ptr_mv
    chunk b ofs mvl (SHAPE: shape_decoding chunk mvl (Vptr b ofs)):
  <<FRAG: forallb is_ptr_mv mvl = true>>.
Proof.
  remember (Vptr b ofs) as v.
  ginduction SHAPE; ss; [|des_ifs]; ii. des_ifs; try by (destruct chunk; ss).
  assert (quantity_eq (quantity_chunk chunk) Q64).
  { destruct chunk; ss. }
  r. repeat rewrite andb_true_iff. splits; auto.
  rewrite forallb_forall. ii. exploit H2; eauto. i. des_safe. inv H4. ss.
Qed.

Lemma ptr_normalize_mv_result_ptr m byte
    (PTR: is_ptr_mv (_decode_normalize_mv m byte) = true):
  <<PTR: is_ptr_mv byte = true>>.
Proof.
  destruct byte; ss. des_ifs; ss; clarify.
  - destruct m0; ss. des_ifs. eapply nth_error_In in Heq0.
    unfold rev_if_be_mv in Heq0. des_ifs_safe. rewrite <- in_rev in Heq0. ss.
    exfalso. eapply inj_bytes_no_fragment'; eauto.
  - destruct m0; ss. des_ifs. eapply nth_error_In in Heq0.
    unfold rev_if_be_mv in Heq0. des_ifs_safe. rewrite <- in_rev in Heq0. ss.
    exfalso. eapply inj_bytes_no_fragment'; eauto.
  - destruct m0; ss. des_ifs. eapply nth_error_In in Heq1.
    unfold rev_if_be_mv in Heq1. des_ifs_safe. rewrite <- in_rev in Heq1. ss.
    exfalso. eapply inj_bytes_no_fragment'; eauto.
Qed.

Lemma ptr_normalize_mvs_result_ptr_aux m bytes
    (PTR: forallb is_ptr_mv (map (_decode_normalize_mv m) bytes) = true):
  <<PTR: forallb is_ptr_mv bytes = true>>.
Proof.
  ginduction bytes; ss; i. eapply andb_prop in PTR. des.
  erewrite IHbytes; eauto. erewrite ptr_normalize_mv_result_ptr; eauto.
Qed.

Lemma ptr_normalize_mvs_result_ptr chunk m bytes
    (PTR: forallb is_ptr_mv (normalize_mvs chunk m bytes) = true):
  <<PTR: forallb is_ptr_mv bytes = true>>.
Proof.
  unfold normalize_mvs in *. des_ifs. eapply ptr_normalize_mvs_result_ptr_aux; eauto.
Qed.

Theorem load_pointer_store:
  forall chunk m1 b ofs v m2 chunk' b' ofs' v_b v_o,
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
  (v = Vptr v_b v_o /\ compat_pointer_chunks chunk chunk' /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').
Proof.
  intros.
  destruct (peq b' b); auto. subst b'.
  destruct (zle (ofs' + size_chunk chunk') ofs); auto.
  destruct (zle (ofs + size_chunk chunk) ofs'); auto.
  exploit load_store_overlap; eauto.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  exploit shape_decoding_pointer_all_ptr_mv; eauto. intros PTR.
  rewrite normalize_mvs_pure in DEC.
  2:{ assert (PTR': forallb is_ptr_mv (mv1' :: mvl') = true).
      { clear - PTR. unfold normalize_mvs in PTR. des_ifs. des.
        remember (mv1' :: mvl') as mvl. clear -PTR. ginduction mvl; ss.
        i. eapply andb_prop in PTR. des. erewrite IHmvl; eauto.
        clear -PTR. destruct a; ss. des_ifs; ss; clarify.
        - ss. exfalso. eapply nth_error_In in Heq0.
          unfold rev_if_be_mv in Heq0. des_ifs_safe. rewrite <- in_rev in Heq0.
          destruct m; ss. des_ifs. eapply inj_bytes_no_fragment'; eauto.
        - ss. exfalso. eapply nth_error_In in Heq0.
          unfold rev_if_be_mv in Heq0. des_ifs_safe. rewrite <- in_rev in Heq0.
          destruct m; ss. des_ifs. eapply inj_bytes_no_fragment'; eauto.
        - des_ifs. ss. exfalso. eapply nth_error_In in Heq1.
          unfold rev_if_be_mv in Heq1. des_ifs_safe. rewrite <- in_rev in Heq1.
          destruct m; ss. des_ifs. eapply inj_bytes_no_fragment'; eauto. }
      left. unfold is_mixed_mvs. rewrite PTR'. ss. eapply andb_false_r. }
  inv DEC; try contradiction.
  destruct CASES as [(A & B) | [(A & B) | (A & B)]].
- (* Same offset *)
  subst. inv ENC.
  assert (chunk = Mint32 \/ chunk = Many32 \/ chunk = Mint64 \/ chunk = Many64)
  by (destruct chunk; auto || contradiction).
  left; split. rewrite H3.
  destruct H4 as [P|[P|[P|P]]]; subst chunk'; destruct v0; simpl in H3;
  try congruence; destruct Archi.ptr64; congruence.
  split. apply compat_pointer_chunks_true; auto.
  auto.
- (* ofs' > ofs *)
  inv ENC.
  + exploit H10; eauto. intros (j & P & Q). inv P. congruence.
  + exploit H8; eauto. intros (n & P); congruence.
  + exploit H2; eauto. congruence.
- (* ofs' < ofs *)
  exploit H7; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence.
Qed.

(* Theorem load_store_pointer_overlap: *)
(*   forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v, *)
(*   store chunk m1 b ofs (Vptr v_b v_o) = Some m2 -> *)
(*   load chunk' m2 b ofs' = Some v -> *)
(*   ofs' <> ofs -> *)
(*   ofs' + size_chunk chunk' > ofs -> *)
(*   ofs + size_chunk chunk > ofs' -> *)
(*   v = Vundef. *)
(* Proof. *)
(* (*   intros. *) *)
(* (*   exploit load_store_overlap; eauto. *) *)
(* (*   intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES). *) *)
(* (*   exploit shape_decoding_pointer_fragment'; eauto. intros FRAG1. *) *)
(* (*   exploit fragment_normalize_fragment; try eapply FRAG1. *) *)
(* (*   { ss. lia. } *) *)
(* (*   intros (mvl'' & FRAG2). erewrite decode_normalize_all_fragment in DEC; eauto. *) *)
(* (*   destruct CASES as [(A & B) | [(A & B) | (A & B)]]. *) *)
(* (* - congruence. *) *)
(* (* - inv ENC. *) *)
(* (*   + exploit H9; eauto. intros (j & P & Q). subst mv1'. inv DEC. congruence. auto. *) *)
(* (*   + contradiction. *) *)
(* (*   + exploit H5; eauto. intros; subst. inv DEC; auto. *) *)
(* (* - inv DEC. *) *)
(* (*   + exploit H10; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence. *) *)
(* (*   + exploit H8; eauto. intros (n & P). subst mv1. inv ENC. contradiction. *) *)
(* (*     + auto. *) *)
(* Qed. *)

(* Theorem load_store_pointer_mismatch: *)
(*   forall chunk m1 b ofs v_b v_o m2 chunk' v, *)
(*   store chunk m1 b ofs (Vptr v_b v_o) = Some m2 -> *)
(*   load chunk' m2 b ofs = Some v -> *)
(*   ~compat_pointer_chunks chunk chunk' -> *)
(*   v = Vundef. *)
(* Proof. *)
(*   intros. *)
(*   exploit load_store_overlap; eauto. *)
(*   generalize (size_chunk_pos chunk'); lia. *)
(*   generalize (size_chunk_pos chunk); lia. *)
(*   intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES). *)
(*   destruct CASES as [(A & B) | [(A & B) | (A & B)]]; try extlia. *)

(* (*   inv ENC; inv DEC; auto. *) *)
(* (* - elim H1. apply compat_pointer_chunks_true; auto. *) *)
(* (* - contradiction. *) *)
(* Qed. *)

Lemma store_similar_chunks:
  forall chunk1 chunk2 v1 v2 m b ofs,
  encode_val chunk1 v1 = encode_val chunk2 v2 ->
  align_chunk chunk1 = align_chunk chunk2 ->
  store chunk1 m b ofs v1 = store chunk2 m b ofs v2.
Proof.
  intros. unfold store.
  assert (size_chunk chunk1 = size_chunk chunk2).
    repeat rewrite size_chunk_conv.
    rewrite <- (encode_val_length chunk1 v1).
    rewrite <- (encode_val_length chunk2 v2).
    congruence.
  unfold store.
  destruct (valid_access_dec m chunk1 b ofs Writable);
  destruct (valid_access_dec m chunk2 b ofs Writable); auto.
  f_equal. apply mkmem_ext; auto. congruence.
  elim n. apply valid_access_compat with chunk1; auto. lia.
  elim n. apply valid_access_compat with chunk2; auto. lia.
Qed.

Theorem store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v.
Proof. intros. apply store_similar_chunks. apply encode_val_int8_signed_unsigned. auto. Qed.

Theorem store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v.
Proof. intros. apply store_similar_chunks. apply encode_val_int16_signed_unsigned. auto. Qed.

Theorem store_int8_zero_ext:
  forall m b ofs n,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int8_zero_ext. auto. Qed.

Theorem store_int8_sign_ext:
  forall m b ofs n,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
  store Mint8signed m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int8_sign_ext. auto. Qed.

Theorem store_int16_zero_ext:
  forall m b ofs n,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int16_zero_ext. auto. Qed.

Theorem store_int16_sign_ext:
  forall m b ofs n,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
  store Mint16signed m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int16_sign_ext. auto. Qed.

(*
Theorem store_float64al32:
  forall m b ofs v m',
  store Mfloat64 m b ofs v = Some m' -> store Mfloat64al32 m b ofs v = Some m'.
Proof.
  unfold store; intros.
  destruct (valid_access_dec m Mfloat64 b ofs Writable); try discriminate.
  destruct (valid_access_dec m Mfloat64al32 b ofs Writable).
  rewrite <- H. f_equal. apply mkmem_ext; auto.
  elim n. apply valid_access_compat with Mfloat64; auto. simpl; lia.
Qed.

Theorem storev_float64al32:
  forall m a v m',
  storev Mfloat64 m a v = Some m' -> storev Mfloat64al32 m a v = Some m'.
Proof.
  unfold storev; intros. destruct a; auto. apply store_float64al32; auto.
Qed.
*)

Lemma storev_concrete chunk m addr v m'
    (STORE: storev chunk m addr v = Some m') :
  <<SAME: mem_concrete m = mem_concrete m'>>.
Proof.
  unfold storev in *. des_ifs; eapply concrete_store; eauto.
Qed.

Lemma storebytes_concrete m b ofs mvl m'
    (STORE: storebytes m b ofs mvl = Some m') :
  <<SAME: mem_concrete m = mem_concrete m'>>.
Proof.
  unfold storebytes in *. des_ifs.
Qed.

(** ** Properties related to [storebytes]. *)

Theorem range_perm_storebytes:
  forall m1 b ofs bytes,
  range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable ->
  { m2 : mem | storebytes m1 b ofs bytes = Some m2 }.
Proof.
  intros. unfold storebytes.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable).
  econstructor; reflexivity.
  contradiction.
Defined.

Theorem storebytes_store:
  forall m1 b ofs chunk v m2,
  storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 b ofs v = Some m2.
Proof.
  unfold storebytes, store. intros.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length (encode_val chunk v))) Cur Writable); inv H.
  destruct (valid_access_dec m1 chunk b ofs Writable).
  f_equal. apply mkmem_ext; auto.
  elim n. constructor; auto.
  rewrite encode_val_length in r. rewrite size_chunk_conv. auto.
Qed.

Theorem store_storebytes:
  forall m1 b ofs chunk v m2,
  store chunk m1 b ofs v = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) = Some m2.
Proof.
  unfold storebytes, store. intros.
  destruct (valid_access_dec m1 chunk b ofs Writable); inv H.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length (encode_val chunk v))) Cur Writable).
  f_equal. apply mkmem_ext; auto.
  destruct v0.  elim n.
  rewrite encode_val_length. rewrite <- size_chunk_conv. auto.
Qed.

Section STOREBYTES.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable bytes: list memval.
Variable m2: mem.
Hypothesis STORE: storebytes m1 b ofs bytes = Some m2.

Lemma storebytes_access: mem_access m2 = mem_access m1.
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Lemma storebytes_mem_contents:
   mem_contents m2 = PMap.set b (setN bytes ofs m1.(mem_contents)#b) m1.(mem_contents).
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem perm_storebytes_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access; auto.
Qed.

Theorem perm_storebytes_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access in H; auto.
Qed.

Local Hint Resolve perm_storebytes_1 perm_storebytes_2: mem.

Theorem concrete_storebytes:
  m1.(mem_concrete) = m2.(mem_concrete).
Proof.
  unfold storebytes in STORE. destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable); inversion STORE.
  reflexivity.
Qed.

Theorem storebytes_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem storebytes_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Local Hint Resolve storebytes_valid_access_1 storebytes_valid_access_2: mem.

Theorem nextblock_storebytes:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem storebytes_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_storebytes; auto.
Qed.

Theorem storebytes_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_storebytes in H; auto.
Qed.

Local Hint Resolve storebytes_valid_block_1 storebytes_valid_block_2: mem.

Theorem storebytes_range_perm:
  range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem loadbytes_storebytes_same:
  loadbytes m2 b ofs (Z.of_nat (length bytes)) = Some bytes.
Proof.
  intros. assert (STORE2:=STORE). unfold storebytes in STORE2. unfold loadbytes.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  try discriminate.
  rewrite pred_dec_true.
  decEq. inv STORE2; simpl. rewrite PMap.gss. rewrite Nat2Z.id.
  apply getN_setN_same.
  red; eauto with mem.
Qed.

Theorem loadbytes_storebytes_disjoint:
  forall b' ofs' len,
  len >= 0 ->
  b' <> b \/ Intv.disjoint (ofs', ofs' + len) (ofs, ofs + Z.of_nat (length bytes)) ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs' (ofs' + len) Cur Readable).
  rewrite pred_dec_true.
  rewrite storebytes_mem_contents. decEq.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  apply getN_setN_disjoint. rewrite Z2Nat.id by lia. intuition congruence.
  auto.
  red; auto with mem.
  apply pred_dec_false.
  red; intros; elim n. red; auto with mem.
Qed.

Theorem loadbytes_storebytes_other:
  forall b' ofs' len,
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Proof.
  intros. apply loadbytes_storebytes_disjoint; auto.
  destruct H0; auto. right. apply Intv.disjoint_range; auto.
Qed.

Theorem load_storebytes_other:
  forall chunk b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' = load chunk m1 b' ofs'.
Proof.
  intros. unfold load.
  exploit storebytes_concrete; eauto. intros CONC.
  erewrite (normalize_mvs_same_concrete m1 m2); eauto.
  destruct (valid_access_dec m1 chunk b' ofs' Readable).
  rewrite pred_dec_true.
  rewrite storebytes_mem_contents. decEq.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  rewrite getN_setN_outside. auto. rewrite <- size_chunk_conv. intuition congruence.
  auto.
  destruct v; split; auto. red; auto with mem.
  apply pred_dec_false.
  red; intros; elim n. destruct H0. split; auto. red; auto with mem.
Qed.

End STOREBYTES.

Lemma setN_concat:
  forall bytes1 bytes2 ofs c,
  setN (bytes1 ++ bytes2) ofs c = setN bytes2 (ofs + Z.of_nat (length bytes1)) (setN bytes1 ofs c).
Proof.
  induction bytes1; intros.
  simpl. decEq. lia.
  simpl length. rewrite Nat2Z.inj_succ. simpl. rewrite IHbytes1. decEq. lia.
Qed.

Theorem storebytes_concat:
  forall m b ofs bytes1 m1 bytes2 m2,
  storebytes m b ofs bytes1 = Some m1 ->
  storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2.
Proof.
  intros. generalize H; intro ST1. generalize H0; intro ST2.
  unfold storebytes; unfold storebytes in ST1; unfold storebytes in ST2.
  destruct (range_perm_dec m b ofs (ofs + Z.of_nat(length bytes1)) Cur Writable); try congruence.
  destruct (range_perm_dec m1 b (ofs + Z.of_nat(length bytes1)) (ofs + Z.of_nat(length bytes1) + Z.of_nat(length bytes2)) Cur Writable); try congruence.
  destruct (range_perm_dec m b ofs (ofs + Z.of_nat (length (bytes1 ++ bytes2))) Cur Writable).
  inv ST1; inv ST2; simpl. decEq. apply mkmem_ext; auto.
  rewrite PMap.gss.  rewrite setN_concat. symmetry. apply PMap.set2.
  elim n.
  rewrite app_length. rewrite Nat2Z.inj_add. red; intros.
  destruct (zlt ofs0 (ofs + Z.of_nat(length bytes1))).
  apply r. lia.
  eapply perm_storebytes_2; eauto. apply r0. lia.
Qed.

Theorem storebytes_split:
  forall m b ofs bytes1 bytes2 m2,
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 = Some m1
  /\ storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 = Some m2.
Proof.
  intros.
  destruct (range_perm_storebytes m b ofs bytes1) as [m1 ST1].
  red; intros. exploit storebytes_range_perm; eauto. rewrite app_length.
  rewrite Nat2Z.inj_add. lia.
  destruct (range_perm_storebytes m1 b (ofs + Z.of_nat (length bytes1)) bytes2) as [m2' ST2].
  red; intros. eapply perm_storebytes_1; eauto. exploit storebytes_range_perm.
  eexact H. instantiate (1 := ofs0). rewrite app_length. rewrite Nat2Z.inj_add. lia.
  auto.
  assert (Some m2 = Some m2').
  rewrite <- H. eapply storebytes_concat; eauto.
  inv H0.
  exists m1; split; auto.
Qed.

Theorem store_int64_split:
  forall m b ofs v m',
  store Mint64 m b ofs v = Some m' -> Archi.ptr64 = false ->
  exists m1,
     store Mint32 m b ofs (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
  /\ store Mint32 m1 b (ofs + 4) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m'.
Proof.
  intros.
  exploit store_valid_access_3; eauto. intros [A B]. simpl in *.
  exploit store_storebytes. eexact H. intros SB.
  rewrite encode_val_int64 in SB by auto.
  exploit storebytes_split. eexact SB. intros [m1 [SB1 SB2]].
  rewrite encode_val_length in SB2. simpl in SB2.
  exists m1; split.
  apply storebytes_store. exact SB1.
  simpl. apply Z.divide_trans with 8; auto. exists 2; auto.
  apply storebytes_store. exact SB2.
  simpl. apply Z.divide_add_r. apply Z.divide_trans with 8; auto. exists 2; auto. exists 1; auto.
Qed.

Theorem storev_int64_split:
  forall m a v m',
  storev Mint64 m a v = Some m' -> Archi.ptr64 = false ->
  exists m1,
     storev Mint32 m a (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
  /\ storev Mint32 m1 (Val.add a (Vint (Int.repr 4))) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m'.
Proof.
  intros. destruct a; simpl in H; inv H. { des_ifs. } rewrite H2.
  exploit store_int64_split; eauto. intros [m1 [A B]].
  exists m1; split.
  exact A.
  unfold storev, Val.add. rewrite H0.
  rewrite addressing_int64_split; auto.
  exploit store_valid_access_3. eexact H2. intros [P Q]. exact Q.
Qed.

(** ** Properties related to [alloc]. *)

Section ALLOC.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Variable b: block.
Hypothesis ALLOC: alloc m1 lo hi = (m2, b).

Theorem nextblock_alloc:
  nextblock m2 = Pos.succ (nextblock m1).
Proof.
  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

Theorem concrete_alloc:
  m1.(mem_concrete) = m2.(mem_concrete).
Proof.
  unfold alloc in ALLOC. inversion ALLOC. reflexivity.
Qed.

Theorem alloc_result:
  b = nextblock m1.
Proof.
  injection ALLOC; auto.
Qed.

Theorem valid_block_alloc:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_alloc.
  apply Plt_trans_succ; auto.
Qed.

Theorem fresh_block_alloc:
  ~(valid_block m1 b).
Proof.
  unfold valid_block. rewrite alloc_result. apply Plt_strict.
Qed.

Theorem valid_new_block:
  valid_block m2 b.
Proof.
  unfold valid_block. rewrite alloc_result. rewrite nextblock_alloc. apply Plt_succ.
Qed.

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.

Theorem valid_block_alloc_inv:
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.
Proof.
  unfold valid_block; intros.
  rewrite nextblock_alloc in H. rewrite alloc_result.
  exploit Plt_succ_inv; eauto. tauto.
Qed.

Theorem perm_alloc_1:
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite PMap.gsspec. destruct (peq b' (nextblock m1)); auto.
  rewrite nextblock_noaccess in H. contradiction. subst b'. apply Plt_strict.
Qed.

Theorem perm_alloc_2:
  forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true.
  rewrite zlt_true. simpl. auto with mem. lia. lia.
Qed.

Theorem perm_alloc_inv:
  forall b' ofs k p,
  perm m2 b' ofs k p ->
  if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p.
Proof.
  intros until p; unfold perm. inv ALLOC. simpl.
  rewrite PMap.gsspec. unfold eq_block. destruct (peq b' (nextblock m1)); intros.
  destruct (zle lo ofs); try contradiction. destruct (zlt ofs hi); try contradiction.
  split; auto.
  auto.
Qed.

Theorem perm_alloc_3:
  forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_true; auto.
Qed.

Theorem perm_alloc_4:
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_false; auto.
Qed.

Local Hint Resolve perm_alloc_1 perm_alloc_2 perm_alloc_3 perm_alloc_4: mem.

Theorem valid_access_alloc_other:
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; auto with mem.
Qed.

Theorem valid_access_alloc_same:
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable.
Proof.
  intros. constructor; auto with mem.
  red; intros. apply perm_alloc_2. lia.
Qed.

Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

Theorem valid_access_alloc_inv:
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p.
Proof.
  intros. inv H.
  generalize (size_chunk_pos chunk); intro.
  destruct (eq_block b' b). subst b'.
  assert (perm m2 b ofs Cur p). apply H0. lia.
  assert (perm m2 b (ofs + size_chunk chunk - 1) Cur p). apply H0. lia.
  exploit perm_alloc_inv. eexact H2. rewrite dec_eq_true. intro.
  exploit perm_alloc_inv. eexact H3. rewrite dec_eq_true. intro.
  intuition lia.
  split; auto. red; intros.
  exploit perm_alloc_inv. apply H0. eauto. rewrite dec_eq_false; auto.
Qed.

Theorem load_alloc_unchanged:
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b' ofs Readable).
  exploit valid_access_alloc_inv; eauto. destruct (eq_block b' b); intros.
  subst b'. elimtype False. eauto with mem.
  rewrite pred_dec_true; auto.
  injection ALLOC; intros. rewrite <- H2; simpl.
  rewrite PMap.gso. auto. rewrite H1. apply not_eq_sym; eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

Theorem load_alloc_other:
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v.
Proof.
  intros. rewrite <- H. apply load_alloc_unchanged. eauto with mem.
Qed.
(* Lemma undef_normalize_to_fragment_undef chunk mvl: *)
(*   exists mvl', <<UNDEF: normalize_to_fragment chunk (Undef :: mvl) = Undef :: mvl'>>. *)
(* Proof. unfold normalize_to_fragment. des_ifs_safe. des_ifs; esplits; eauto. Qed. *)

Theorem load_alloc_same:
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef.
Proof.
  intros. exploit load_result; eauto. intro. rewrite H0.
  injection ALLOC; intros. rewrite <- H2; simpl. rewrite <- H1.
  rewrite PMap.gss. destruct (size_chunk_nat_pos chunk) as [n E]. rewrite E. simpl.
  rewrite ZMap.gi. rewrite H2. specialize (normalize_mvs_undef m2 chunk (getN n (ofs + 1) (ZMap.init Undef))). i.
  des. rewrite H3. apply decode_val_undef.
Qed.

Theorem load_alloc_same':
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef.
Proof.
  intros. assert (exists v, load chunk m2 b ofs = Some v).
    apply valid_access_load. constructor; auto.
    red; intros. eapply perm_implies. apply perm_alloc_2. lia. auto with mem.
  destruct H2 as [v LOAD]. rewrite LOAD. decEq.
  eapply load_alloc_same; eauto.
Qed.

Theorem loadbytes_alloc_unchanged:
  forall b' ofs n,
  valid_block m1 b' ->
  loadbytes m2 b' ofs n = loadbytes m1 b' ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  injection ALLOC; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso. auto. rewrite A. eauto with mem.
  red; intros. eapply perm_alloc_1; eauto.
  rewrite pred_dec_false; auto.
  red; intros; elim n0. red; intros. eapply perm_alloc_4; eauto. eauto with mem.
Qed.

Theorem loadbytes_alloc_same:
  forall n ofs bytes byte,
  loadbytes m2 b ofs n = Some bytes ->
  In byte bytes -> byte = Undef.
Proof.
  unfold loadbytes; intros. destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
  revert H0.
  injection ALLOC; intros A B. rewrite <- A; rewrite <- B; simpl. rewrite PMap.gss.
  generalize (Z.to_nat n) ofs. induction n0; simpl; intros.
  contradiction.
  rewrite ZMap.gi in H0. destruct H0; eauto.
Qed.

End ALLOC.

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.
Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

(** ** Properties related to [free]. *)

Theorem range_perm_free:
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  { m2: mem | free m1 b lo hi = Some m2 }.
Proof.
  intros; unfold free. rewrite pred_dec_true; auto. econstructor; eauto.
Defined.

Section FREE.

Variable m1: mem.
Variable bf: block.
Variables lo hi: Z.
Variable m2: mem.
Hypothesis FREE: free m1 bf lo hi = Some m2.

Theorem free_range_perm:
  range_perm m1 bf lo hi Cur Freeable.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Cur Freeable); auto.
  congruence.
Qed.

Lemma free_result:
  m2 = unchecked_free m1 bf lo hi.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Cur Freeable).
  congruence. congruence.
Qed.

Theorem concrete_free:
  m1.(mem_concrete) = m2.(mem_concrete).
Proof.
  unfold free, unchecked_free in FREE.
  destruct (range_perm_dec m1 bf lo hi Cur Freeable); inversion FREE.
  reflexivity.
Qed.

Theorem nextblock_free:
  nextblock m2 = nextblock m1.
Proof.
  rewrite free_result; reflexivity.
Qed.

Theorem valid_block_free_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Proof.
  intros. rewrite free_result. assumption.
Qed.

Theorem valid_block_free_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Proof.
  intros. rewrite free_result in H. assumption.
Qed.

Local Hint Resolve valid_block_free_1 valid_block_free_2: mem.

Theorem perm_free_1:
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl.
  elimtype False; intuition.
  auto. auto.
  auto.
Qed.

Theorem perm_free_2:
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true. rewrite zlt_true.
  simpl. tauto. lia. lia.
Qed.

Theorem perm_free_3:
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p.
Proof.
  intros until p. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl. tauto.
  auto. auto. auto.
Qed.

Theorem perm_free_inv:
  forall b ofs k p,
  perm m1 b ofs k p ->
  (b = bf /\ lo <= ofs < hi) \/ perm m2 b ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf); auto. subst b.
  destruct (zle lo ofs); simpl; auto.
  destruct (zlt ofs hi); simpl; auto.
Qed.

Theorem valid_access_free_1:
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p ->
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; intros. eapply perm_free_1; eauto.
  destruct (zlt lo hi). intuition. right. lia.
Qed.

Theorem valid_access_free_2:
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p).
Proof.
  intros; red; intros. inv H2.
  generalize (size_chunk_pos chunk); intros.
  destruct (zlt ofs lo).
  elim (perm_free_2 lo Cur p).
  lia. apply H3. lia.
  elim (perm_free_2 ofs Cur p).
  lia. apply H3. lia.
Qed.

Theorem valid_access_free_inv_1:
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p.
Proof.
  intros. destruct H. split; auto.
  red; intros. generalize (H ofs0 H1).
  rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs0); simpl.
  destruct (zlt ofs0 hi); simpl.
  tauto. auto. auto. auto.
Qed.

Theorem valid_access_free_inv_2:
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.
Proof.
  intros.
  destruct (zlt lo hi); auto.
  destruct (zle (ofs + size_chunk chunk) lo); auto.
  destruct (zle hi ofs); auto.
  elim (valid_access_free_2 chunk ofs p); auto. lia.
Qed.

Theorem load_free:
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b ofs Readable).
  rewrite pred_dec_true.
  rewrite free_result; auto.
  eapply valid_access_free_inv_1; eauto.
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_free_1; eauto.
Qed.

Theorem load_free_2:
  forall chunk b ofs v,
  load chunk m2 b ofs = Some v -> load chunk m1 b ofs = Some v.
Proof.
  intros. unfold load. rewrite pred_dec_true.
  rewrite (load_result _ _ _ _ _ H). rewrite free_result; auto.
  apply valid_access_free_inv_1. eauto with mem.
Qed.

Theorem loadbytes_free:
  forall b ofs n,
  b <> bf \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
  loadbytes m2 b ofs n = loadbytes m1 b ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  rewrite free_result; auto.
  red; intros. eapply perm_free_3; eauto.
  rewrite pred_dec_false; auto.
  red; intros. elim n0; red; intros.
  eapply perm_free_1; eauto. destruct H; auto. right; lia.
Qed.

Theorem loadbytes_free_2:
  forall b ofs n bytes,
  loadbytes m2 b ofs n = Some bytes -> loadbytes m1 b ofs n = Some bytes.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
  rewrite pred_dec_true. rewrite free_result; auto.
  red; intros. apply perm_free_3; auto.
Qed.

End FREE.

Local Hint Resolve valid_block_free_1 valid_block_free_2
             perm_free_1 perm_free_2 perm_free_3
             valid_access_free_1 valid_access_free_inv_1: mem.

(** ** Properties related to [drop_perm] *)

Theorem range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' -> range_perm m b lo hi Cur Freeable.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec m b lo hi Cur Freeable). auto. discriminate.
Qed.

Theorem range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> {m' | drop_perm m b lo hi p = Some m' }.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec m b lo hi Cur Freeable). econstructor. eauto. contradiction.
Defined.

Section DROP.

Variable m: mem.
Variable b: block.
Variable lo hi: Z.
Variable p: permission.
Variable m': mem.
Hypothesis DROP: drop_perm m b lo hi p = Some m'.

Theorem nextblock_drop:
  nextblock m' = nextblock m.
Proof.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP; auto.
Qed.

Theorem concrete_drop:
  m.(mem_concrete) = m'.(mem_concrete).
Proof.
  unfold drop_perm in DROP.
  destruct (range_perm_dec m b lo hi Cur Freeable) in DROP; inversion DROP.
  reflexivity.
Qed.

Theorem drop_perm_valid_block_1:
  forall b', valid_block m b' -> valid_block m' b'.
Proof.
  unfold valid_block; rewrite nextblock_drop; auto.
Qed.

Theorem drop_perm_valid_block_2:
  forall b', valid_block m' b' -> valid_block m b'.
Proof.
  unfold valid_block; rewrite nextblock_drop; auto.
Qed.

Theorem perm_drop_1:
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  unfold perm. simpl. rewrite PMap.gss. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true. simpl. constructor.
  lia. lia.
Qed.

Theorem perm_drop_2:
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  revert H0. unfold perm; simpl. rewrite PMap.gss. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true. simpl. auto.
  lia. lia.
Qed.

Theorem perm_drop_3:
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  unfold perm; simpl. rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  byContradiction. intuition lia.
  auto. auto. auto.
Qed.

Theorem perm_drop_4:
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  revert H. unfold perm; simpl. rewrite PMap.gsspec. destruct (peq b' b).
  subst b'. unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  simpl. intros. apply perm_implies with p. apply perm_implies with Freeable. apply perm_cur.
  apply r. tauto. auto with mem. auto.
  auto. auto. auto.
Qed.

Lemma valid_access_drop_1:
  forall chunk b' ofs p',
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p p' ->
  valid_access m chunk b' ofs p' -> valid_access m' chunk b' ofs p'.
Proof.
  intros. destruct H0. split; auto.
  red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. lia.
  generalize (size_chunk_pos chunk); intros. intuition.
  eapply perm_drop_3; eauto.
Qed.

Lemma valid_access_drop_2:
  forall chunk b' ofs p',
  valid_access m' chunk b' ofs p' -> valid_access m chunk b' ofs p'.
Proof.
  intros. destruct H; split; auto.
  red; intros. eapply perm_drop_4; eauto.
Qed.

Theorem load_drop:
  forall chunk b' ofs,
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs.
Proof.
  intros.
  unfold load.
  destruct (valid_access_dec m chunk b' ofs Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP. simpl. auto.
  eapply valid_access_drop_1; eauto.
  rewrite pred_dec_false. auto.
  red; intros; elim n. eapply valid_access_drop_2; eauto.
Qed.

Theorem loadbytes_drop:
  forall b' ofs n,
  b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable ->
  loadbytes m' b' ofs n = loadbytes m b' ofs n.
Proof.
  intros.
  unfold loadbytes.
  destruct (range_perm_dec m b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP. simpl. auto.
  red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. lia. intuition.
  eapply perm_drop_3; eauto.
  rewrite pred_dec_false; eauto.
  red; intros; elim n0; red; intros.
  eapply perm_drop_4; eauto.
Qed.

End DROP.

Lemma denormalize_store_other
  m z b ofs b' ofs' chunk v m'
  (DENO: denormalize z m = Some (b, ofs))
  (STORE: store chunk m b' ofs' v = Some m')
  :
  <<DENO': denormalize z m' = Some (b, ofs)>>.
Proof.
  eapply denormalize_info in DENO. des.
  eapply ptr2int_to_denormalize_max; eauto.
- unfold ptr2int. erewrite concrete_store in CONC; eauto.
  rewrite CONC. f_equal. lia.
- eapply perm_store_1; eauto.
Qed.

Lemma denormalize_storebytes_other
  m z b ofs b' ofs' vl m'
  (DENO: denormalize z m = Some (b, ofs))
  (STORE: storebytes m b' ofs' vl = Some m')
  :
  <<DENO': denormalize z m' = Some (b, ofs)>>.
Proof.
  eapply denormalize_info in DENO. des.
  eapply ptr2int_to_denormalize_max; eauto.
- unfold ptr2int. erewrite concrete_storebytes in CONC; eauto.
  rewrite CONC. f_equal. lia.
- eapply perm_storebytes_1; eauto.
Qed.

Section CAPTURE.
  Variable chunk: memory_chunk.
  Variable m1:mem.
  Variable m2:mem.
  Variable b:block.
  Variable addr:Z.
  Hypothesis CAPTURE: capture m1 b addr m2.

  Theorem nextblock_capture:
    nextblock m2 = nextblock m1.
  Proof.
    inv CAPTURE. ss.
  Qed.

  Theorem loadbytes_capture_unchanged:
    forall b1 ofs1 n,
      loadbytes m2 b1 ofs1 n = loadbytes m1 b1 ofs1 n.
  Proof.
    i. inv CAPTURE.
    i. unfold loadbytes. des_ifs.
    - rewrite CONTENTS. eauto.
    - unfold range_perm, perm, perm_order' in *.
      rewrite <- ACCESS in r.
      exfalso. eapply n0. eauto.
    - unfold range_perm, perm, perm_order' in *.
      rewrite ACCESS in r.
      exfalso. eapply n0. eauto.
  Qed.

  Lemma concrete_other :
    forall blk, (blk<>b -> m1.(mem_concrete)!blk = m2.(mem_concrete)!blk).
  Proof.
    i. inv CAPTURE.
    destruct ((mem_concrete m1)!b).
    - exploit PREVADDR; eauto. i. des. subst. rewrite H1. auto.
    - exploit CAPTURED; auto. i. rewrite H0.
      exploit PTree.gso; eauto.
  Qed.

End CAPTURE.

Lemma capture_trans_store
      m1 m2 m b addr1 addr2 chunk blk ofs v1 v2 m1'
      (CAPTURE1: Mem.capture m b addr1 m1)
      (CAPTURE2: Mem.capture m b addr2 m2)
      (STORE: Mem.store chunk m1 blk ofs v1 = Some m1')
  :
    exists m2', Mem.store chunk m2 blk ofs v2 = Some m2'.
Proof.
  inv CAPTURE1. inv CAPTURE2. eexists.
  unfold Mem.store in *. des_ifs. exfalso. eapply n.
  unfold Mem.valid_access in *. des. split; eauto. unfold Mem.range_perm in *. i.
  unfold Mem.perm in *. rewrite <- ACCESS0. rewrite ACCESS. eauto.
Qed.


(** * Generic injections *)

(** A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address.
*)

Record mem_inj (f: meminj) (m1 m2: mem) : Prop :=
  mk_mem_inj {
    mi_perm:
      forall b1 b2 delta ofs k p,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs k p ->
      perm m2 b2 (ofs + delta) k p;
    mi_align:
      forall b1 b2 delta chunk ofs p,
      f b1 = Some(b2, delta) ->
      range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p ->
      (align_chunk chunk | delta);
    mi_memval:
      forall b1 ofs b2 delta,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs Cur Readable ->
      memval_inject f (ZMap.get ofs m1.(mem_contents)#b1) (ZMap.get (ofs+delta) m2.(mem_contents)#b2);
  }.

(** Preservation of permissions *)

Lemma perm_inj:
  forall f m1 m2 b1 ofs k p b2 delta,
  mem_inj f m1 m2 ->
  perm m1 b1 ofs k p ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) k p.
Proof.
  intros. eapply mi_perm; eauto.
Qed.

Lemma range_perm_inj:
  forall f m1 m2 b1 lo hi k p b2 delta,
  mem_inj f m1 m2 ->
  range_perm m1 b1 lo hi k p ->
  f b1 = Some(b2, delta) ->
  range_perm m2 b2 (lo + delta) (hi + delta) k p.
Proof.
  intros; red; intros.
  replace ofs with ((ofs - delta) + delta) by lia.
  eapply perm_inj; eauto. apply H0. lia.
Qed.

Lemma valid_access_inj:
  forall f m1 m2 b1 b2 delta chunk ofs p,
  mem_inj f m1 m2 ->
  f b1 = Some(b2, delta) ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. destruct H1 as [A B]. constructor.
  replace (ofs + delta + size_chunk chunk)
     with ((ofs + size_chunk chunk) + delta) by lia.
  eapply range_perm_inj; eauto.
  apply Z.divide_add_r; auto. eapply mi_align; eauto with mem.
Qed.

(** Preservation of loads. *)

Lemma getN_inj:
  forall f m1 m2 b1 b2 delta,
  mem_inj f m1 m2 ->
  f b1 = Some(b2, delta) ->
  forall n ofs,
  range_perm m1 b1 ofs (ofs + Z.of_nat n) Cur Readable ->
  list_forall2 (memval_inject f)
               (getN n ofs (m1.(mem_contents)#b1))
               (getN n (ofs + delta) (m2.(mem_contents)#b2)).
Proof.
  induction n; intros; simpl.
  constructor.
  rewrite Nat2Z.inj_succ in H1.
  constructor.
  eapply mi_memval; eauto.
  apply H1. lia.
  replace (ofs + delta + 1) with ((ofs + 1) + delta) by lia.
  apply IHn. red; intros; apply H1; lia.
Qed.

Lemma long_proj_long_fragment q l i
    (LONG: proj_value q l = Vlong i) :
  <<LONG: forallb is_long_mv l = true>>.
Proof.
  unfold proj_value in LONG. des_ifs.
  remember (Fragment (Vlong i) q0 n :: l0) as l. clear - Heq.
  revert Heq. generalize (size_quantity_nat q). ginduction l; i; [ss|].
  destruct n; ss. des_ifs; ss. des_ifs.
  repeat rewrite andb_true_iff in Heq. des. erewrite IHl; eauto.
Qed.

Lemma long_proj_intptr_fragment l i
    (SF: Archi.ptr64 = true) (LONG: proj_value Q64 l = Vlong i) :
  <<LONG: forallb is_intptr_mv l = true>>.
Proof.
  unfold proj_value in LONG. des_ifs.
  remember (Fragment (Vlong i) q n :: l0) as l. unfold is_intptr_mv.
  rewrite SF. simpl. clear - Heq.
  revert Heq. generalize (size_quantity_nat Q64). ginduction l; i; [ss|].
  destruct n; ss. des_ifs; ss. des_ifs.
  repeat rewrite andb_true_iff in Heq. des. erewrite IHl; eauto.
  destruct q; ss.
Qed.

Lemma ptr_proj_ptr_fragment l b ofs
    (PTR: proj_value Q64 l = Vptr b ofs) :
  <<PTR: forallb is_ptr_mv l = true>>.
Proof.
  unfold proj_value in PTR. des_ifs.
  remember (Fragment (Vptr b ofs) q n :: l0) as l. clear - Heq.
  revert Heq. generalize (size_quantity_nat Q64). ginduction l; i; [ss|].
  destruct n; ss. des_ifs; ss. des_ifs.
  repeat rewrite andb_true_iff in Heq. des. erewrite IHl; eauto.
  destruct q; ss.
Qed.

Lemma change_check_fail_normalize_mvs_same chunk mvs
    (UNCHANGE: change_check chunk mvs = false):
  forall m1 m2, normalize_mvs chunk m1 mvs = normalize_mvs chunk m2 mvs.
Proof.
  ii. unfold change_check in UNCHANGE. do 2 rewrite andb_false_iff in UNCHANGE. des.
  - unfold normalize_mvs, normalize_check in *. rewrite UNCHANGE. ss.
  - rewrite negb_false_iff in UNCHANGE. do 2 (erewrite normalize_mvs_pure; eauto).
  - unfold qarchi in UNCHANGE. des_ifs_safe. unfold normalize_mvs, normalize_check. des_ifs_safe.
    destruct chunk; ss.
    + des_ifs; try by (unfold proj_value in Heq1; des_ifs).
      * destruct mvs; try by ss.
        exfalso. rewrite negb_false_iff in UNCHANGE. eapply andb_prop in Heq0. des.
        clear - UNCHANGE Heq0. ginduction mvs; ss; i.
        { destruct m; ss. }
        { destruct m; ss; eauto. eapply andb_prop in Heq0. des; eauto. }
      * exploit long_proj_intptr_fragment; eauto. i. eapply intptr_normalize_mvs_same_aux2; eauto.
      * exploit ptr_proj_ptr_fragment; eauto. i. exfalso. unfold is_mixed_mvs in Heq0.
        rewrite H in Heq0. ss. erewrite andb_false_r in Heq0. clarify.
    + des_ifs; try by (unfold proj_value in Heq1; des_ifs).
      * destruct mvs; try by ss.
        exfalso. rewrite negb_false_iff in UNCHANGE. eapply andb_prop in Heq0. des.
        clear - UNCHANGE Heq0. ginduction mvs; ss; i.
        { destruct m; ss. }
        { destruct m; ss; eauto. eapply andb_prop in Heq0. des; eauto. }
      * exploit long_proj_intptr_fragment; eauto. i. eapply intptr_normalize_mvs_same_aux2; eauto.
      * exploit ptr_proj_ptr_fragment; eauto. i. exfalso. unfold is_mixed_mvs in Heq0.
        rewrite H in Heq0. ss. erewrite andb_false_r in Heq0. clarify.
Qed.
    
Lemma ptrlike_inject_ptrlike f vl1 vl2
    (MVINJ : list_forall2 (memval_inject f) vl1 vl2)
    (UNDEF : ~ In Undef vl1) (UNDEF' : forall q n, ~ In (Fragment Vundef q n) vl1):
  <<MIX: forallb is_ptrlike_mv vl1 = forallb is_ptrlike_mv vl2>>.
Proof.
  ginduction MVINJ; ss. ii. inv H; ss.
  - eapply IHMVINJ; eauto. ii. eapply UNDEF'. eauto.
  - inv H0; ss.
    + r. erewrite IHMVINJ; eauto. ii. eapply UNDEF'; eauto.
    + erewrite IHMVINJ; eauto. ii. eapply UNDEF'; eauto.
    + exfalso. eapply UNDEF'; eauto.
  - exfalso. eapply UNDEF. eauto.
Qed.

Lemma intptr_inject_intptr f vl1 vl2
    (MVINJ : list_forall2 (memval_inject f) vl1 vl2)
    (UNDEF : ~ In Undef vl1) (UNDEF' : forall q n, ~ In (Fragment Vundef q n) vl1):
  <<MIX: forallb is_intptr_mv vl1 = forallb is_intptr_mv vl2>>.
Proof.
  ginduction MVINJ; ss. ii. inv H; ss.
  - inv H0; ss. { rewrite IHMVINJ; eauto. ii. eapply UNDEF'; eauto. }
    exfalso. eapply UNDEF'. eauto.
  - exfalso. eapply UNDEF. eauto.
Qed.

Lemma ptr_inject_ptr f vl1 vl2
    (MVINJ : list_forall2 (memval_inject f) vl1 vl2)
    (UNDEF : ~ In Undef vl1) (UNDEF' : forall q n, ~ In (Fragment Vundef q n) vl1):
  <<MIX: forallb is_ptr_mv vl1 = forallb is_ptr_mv vl2>>.
Proof.
  ginduction MVINJ; ss. ii. inv H; ss.
  - inv H0; ss. { rewrite IHMVINJ; eauto. ii. eapply UNDEF'; eauto. }
    exfalso. eapply UNDEF'. eauto.
  - exfalso. eapply UNDEF. eauto.
Qed.

Lemma byte_inject_byte f vl1 vl2
    (MVINJ : list_forall2 (memval_inject f) vl1 vl2)
    (UNDEF : ~ In Undef vl1) (UNDEF' : forall q n, ~ In (Fragment Vundef q n) vl1):
  <<MIX: forallb is_byte_mv vl1 = forallb is_byte_mv vl2>>.
Proof.
  ginduction MVINJ; ss. ii. inv H; ss.
  - rewrite IHMVINJ; eauto. ii. eapply UNDEF'; eauto.
  - exfalso. eapply UNDEF. eauto.
Qed.
  
Lemma mix_inject_mix f vl1 vl2
    (MVINJ : list_forall2 (memval_inject f) vl1 vl2)
    (UNDEF : ~ In Undef vl1) (UNDEF' : forall q n, ~ In (Fragment Vundef q n) vl1):
  <<MIX: is_mixed_mvs vl1 = is_mixed_mvs vl2>>.
Proof.
  unfold is_mixed_mvs. erewrite ptrlike_inject_ptrlike, ptr_inject_ptr; eauto.
Qed.

Lemma proj_value_undef_frag q' n q vl (FRAG: In (Fragment Vundef q' n) vl):
  <<UNDEF: proj_value q vl = Vundef>>.
Proof.
  unfold proj_value. des_ifs. remember (size_quantity_nat q). clear Heqn1.
  remember (Fragment v q0 n0 :: l) as l'. clear Heql'. ginduction n1; ss; i; des_ifs.
  des_ifs. ss. repeat (eapply andb_prop in Heq; des_safe).
  des; clarify; [destruct v; ss|]. eapply IHn1; eauto.
Qed.

(* move *)
Lemma mixed_ptrlikes
  mvs (MIX: is_mixed_mvs mvs = true):
  <<PTR: forallb is_ptrlike_mv mvs = true>>.
Proof. unfold is_mixed_mvs in MIX. repeat (eapply andb_prop in MIX; des). eauto. Qed.
        
(* Lemma memval_inject_normalize *)
(*   f m1 m2 mv1 mv2 *)
(*   (CONC: forall b1 b2 delta addr, *)
(*       f b1 = Some (b2, delta) -> valid_block m1 b1 -> *)
(*       m1.(mem_concrete)!b1 = Some addr -> *)
(*       m2.(mem_concrete)!b2 = Some (addr-delta)) *)
(*   (MVINJ: memval_inject f mv1 mv2): *)
(*   <<MVINJ: memval_inject f (_decode_normalize_mv m1 mv1) (_decode_normalize_mv m2 mv2)>>. *)
(* Proof. *)
(*   (* inv MVINJ; ss; try econs. inv H; ss; try by econs. *) *)
(*   (* "false. src concrete look up fail but tgt success: src -> Vptr frag / tgt -> byte. memval bind needed". *) *)
(* Abort. *)

Lemma normalize_result_fragments
  mvs m (FRAG: forallb is_frag_mv (map (_decode_normalize_mv m) mvs) = true):
  <<EQ: map (_decode_normalize_mv m) mvs = mvs>>.
Proof.
  ginduction mvs; ss; i. eapply andb_prop in FRAG. des. rewrite IHmvs; eauto.
  r. f_equal. destruct a; ss. des_ifs. destruct v; ss; clarify.
  - ss. exploit nth_error_In; eauto. i. destruct m0; ss.
    unfold rev_if_be_mv in *. des_ifs_safe. rewrite <- in_rev in H.
    exfalso. eapply inj_bytes_no_fragment; eauto. rewrite encode_int_length. lia.
  - ss. exploit nth_error_In; eauto. i. destruct m0; ss.
    unfold rev_if_be_mv in *. des_ifs_safe. rewrite <- in_rev in H.
    exfalso. eapply inj_bytes_no_fragment; eauto. rewrite encode_int_length. lia.
  - ss. des_ifs. exploit nth_error_In; eauto. i. destruct m0; ss.
    unfold rev_if_be_mv in *. des_ifs_safe. rewrite <- in_rev in H.
    exfalso. eapply inj_bytes_no_fragment; eauto. rewrite encode_int_length. lia.
Qed.

Lemma not_bytes_proj_bytes_fail vl (MIXED: forallb is_byte_mv vl = false):
  <<FAIL: proj_bytes vl = None>>.
Proof.
  ginduction vl; ss. ii. eapply andb_false_iff in MIXED. des; des_ifs. exploit IHvl; eauto. i. clarify.
Qed.

Lemma not_bytes_proj_bytes_iff vl:
  proj_bytes vl = None <-> forallb is_byte_mv vl = false.
Proof.
  split; i. 2:{ eapply not_bytes_proj_bytes_fail; eauto. }
  ginduction vl; ss; ii. des_ifs. ss. eauto.
Qed.

Lemma mixed_check_value byte bytes n v q
    (MIXED: is_mixed_mvs_old (byte :: bytes) = true):
  <<FAIL: check_value n v q (byte :: bytes) = false>>.
Proof.
  ginduction n; ss; i. destruct byte; ss. destruct bytes; ss.
  { unfold is_mixed_mvs_old, is_ptrlike_mv in MIXED. ss. des_ifs; destruct q0; ss. }
  destruct (Val.eq v v0); destruct (quantity_eq q q0); ss.
  destruct (Nat.eqb n n0) eqn:N; ss. rewrite Nat.eqb_eq in N. subst v0 q0 n0.
  destruct (is_mixed_mvs_old (m :: bytes)) eqn:MIXED'; [eapply IHn; eauto|].
  clear IHn. unfold is_mixed_mvs_old in MIXED, MIXED'. ss.
  repeat rewrite andb_true_iff in MIXED. des. repeat rewrite negb_true_iff in MIXED1, MIXED0.
  repeat rewrite andb_false_iff in MIXED'. des; clarify.
  - rewrite negb_false_iff in MIXED'. eapply andb_prop in MIXED'. des.
    destruct m; ss. destruct n; ss.
  - rewrite negb_false_iff in MIXED'. eapply andb_prop in MIXED'. des.
    rewrite andb_false_iff in MIXED1. des; clarify. des_ifs_safe.
    destruct m; ss. des_ifs; destruct n; ss. destruct q, q0; ss.
  - rewrite negb_false_iff in MIXED'. eapply andb_prop in MIXED'. des.
    rewrite andb_false_iff in MIXED0. des; clarify. des_ifs_safe.
    destruct m; ss. des_ifs; destruct n; ss. destruct q, q0; ss.
Qed.

Lemma mixed_decode_val_undefs vl chunk (MIXED: is_mixed_mvs_old vl = true):
  <<UNDEF: decode_val chunk vl = Vundef>>.
Proof.
  assert (proj_bytes vl = None).
  { unfold is_mixed_mvs_old in MIXED. repeat rewrite andb_true_iff in MIXED. des.
    rewrite negb_true_iff in *. eapply not_bytes_proj_bytes_fail; ss. }
  unfold decode_val. rewrite H. unfold proj_value. destruct vl; [ss|].
  des_ifs; erewrite mixed_check_value in *; eauto; clarify.
Qed.

Lemma proj_bytes_undef bl (IN: In Undef bl):
  <<BYTES: proj_bytes bl = None>>.
Proof. ginduction bl; ss; ii. des; subst; des_ifs. eapply IHbl in IN; clarify. Qed.

Lemma proj_bytes_fragment v q n bl (IN: In (Fragment v q n) bl) : <<BYTES: proj_bytes bl = None>>.
Proof.
  ginduction bl; ss; ii. des; subst; eauto. exploit IHbl; eauto. i. rewrite H. des_ifs.
Qed.

Lemma in_undef_normalize_in_undef chunk m vl (IN: In Undef vl) :
  <<UNDEF: In Undef (normalize_mvs chunk m vl)>>.
Proof.
  dup IN. eapply in_map with (f:= (_decode_normalize_mv m)) in IN.
  unfold normalize_mvs. des_ifs; ss.
Qed.

Lemma in_undef_frag_normalize_in_undef chunk m vl q n (IN: In (Fragment Vundef q n) vl) :
  <<UNDEF: In (Fragment Vundef q n) (normalize_mvs chunk m vl)>>.
Proof.
  dup IN. eapply in_map with (f:= (_decode_normalize_mv m)) in IN.
  unfold normalize_mvs. des_ifs; ss.
Qed.

Lemma normalized_intptr_undef chunk m vl
    (LEN: (Datatypes.length vl > 0)%nat)
    (NC: normalize_check chunk vl = true)
    (IP : forallb is_intptr_mv (map (_decode_normalize_mv m) vl) = true):
  <<UNDEF: decode_val chunk (map (_decode_normalize_mv m) vl) = Vundef>>.
Proof.
  unfold normalize_check in NC. des_ifs; ss.
  - unfold decode_val. erewrite not_bytes_proj_bytes_fail; eauto.
    2:{ destruct vl; [ss; lia|]. rewrite forallb_false_forall. ii. rewrite forallb_forall in IP.
        ss. exploit IP; eauto. i. exploit H; eauto. i. destruct m0; ss. des_ifs. destruct m0; ss. }
    des_ifs. destruct vl; [ss|]. simpl in IP. destruct m0; simpl in IP; clarify.
    eapply andb_prop in IP. des. des_ifs.
    { exfalso. destruct v; ss; clarify.
      - ss. clear - Heq1 IP. unfold rev_if_be_mv in Heq1. des_ifs; ss.
        eapply nth_error_In in Heq1. rewrite <- in_rev in Heq1.
        unfold encode_int in Heq1. ss. unfold rev_if_be in Heq1. des_ifs. destruct m0; ss. des; clarify.
      - des_ifs. ss. clear - Heq1 IP. unfold rev_if_be_mv in Heq1. des_ifs; ss.
        eapply nth_error_In in Heq1. rewrite <- in_rev in Heq1.
        unfold encode_int in Heq1. ss. unfold rev_if_be in Heq1. des_ifs. destruct m0; ss. des; clarify. }
    { unfold proj_value. simpl in IP. des_ifs. simpl in Heq0. clarify.
      simpl in Heq2, Heq1. rewrite Heq1 in Heq2. clarify. (* simpl in Heq3. *)
      (* n0 is not 7 *)
      rewrite nth_error_None in Heq1. unfold rev_if_be_mv in Heq1. des_ifs.
      rewrite rev_length, length_inj_bytes, encode_int_length in Heq1.
      simpl in Heq3. repeat rewrite andb_true_iff in Heq3. des. clear - Heq4 Heq1.
      des_ifs; lia. }
    { exfalso. destruct v; ss. }
  - unfold decode_val. erewrite not_bytes_proj_bytes_fail; eauto.
    2:{ destruct vl; [ss; lia|]. rewrite forallb_false_forall. ii. rewrite forallb_forall in IP.
        ss. exploit IP; eauto. i. exploit H; eauto. i. destruct m0; ss. des_ifs. destruct m0; ss. }
    des_ifs. destruct vl; [ss|]. simpl in IP. destruct m0; simpl in IP; clarify.
    eapply andb_prop in IP. des. des_ifs.
    { exfalso. destruct v; ss; clarify.
      - ss. clear - Heq0 IP. unfold rev_if_be_mv in Heq0. des_ifs; ss.
        eapply nth_error_In in Heq0. rewrite <- in_rev in Heq0.
        unfold encode_int in Heq0. ss. unfold rev_if_be in Heq0. des_ifs. destruct m0; ss; des; clarify.
      - des_ifs. ss. clear - Heq0 IP. unfold rev_if_be_mv in Heq0. des_ifs; ss.
        eapply nth_error_In in Heq0. rewrite <- in_rev in Heq0.
        unfold encode_int in Heq0. ss. unfold rev_if_be in Heq0. des_ifs. destruct m0; ss. des; clarify. }
    { unfold proj_value. simpl in IP. des_ifs. simpl in Heq. clarify.
      simpl in Heq0, Heq1. rewrite Heq0 in Heq1. clarify. (* simpl in Heq2. *)
      (* n0 is not 7 *)
      rewrite nth_error_None in Heq0. unfold rev_if_be_mv in Heq0. des_ifs.
      rewrite rev_length, length_inj_bytes, encode_int_length in Heq0.
      simpl in Heq2. repeat rewrite andb_true_iff in Heq2. des. clear - Heq3 Heq0.
      des_ifs; lia. }
    { exfalso. destruct v; ss. }
Qed.

Lemma normalize_mvs_decode_val_inject
    f m1 m2 vl1 vl2 chunk
    (LEN: (Datatypes.length vl1 > 0)%nat)
    (CONC: forall b1 b2 delta addr,
        f b1 = Some (b2, delta) -> valid_block m1 b1 ->
        m1.(mem_concrete)!b1 = Some addr ->
        m2.(mem_concrete)!b2 = Some (addr-delta))
    (MVINJ: list_forall2 (memval_inject f) vl1 vl2):
  <<VINJ: Val.inject f (decode_val chunk (normalize_mvs chunk m1 vl1))
                       (decode_val chunk (normalize_mvs chunk m2 vl2))>>.
Proof.
  destruct (classic (In Undef vl1)); rename H into UNDEF1.
  { exploit (in_undef_normalize_in_undef chunk m1); eauto. i. unfold decode_val.
    rewrite proj_bytes_undef; eauto. do 2 (rewrite proj_value_undef; eauto). des_ifs; econs. }
  destruct (classic (forall q n, ~ In (Fragment Vundef q n) vl1)); rename H into UNDEF2; cycle 1.
  { do 2 (eapply not_all_ex_not in UNDEF2; des). eapply NNPP in UNDEF2.
    exploit (in_undef_frag_normalize_in_undef chunk m1); eauto. i. des. unfold decode_val.
    erewrite proj_bytes_fragment; eauto. do 2 (erewrite proj_value_undef_frag; eauto). des_ifs; econs. }
  destruct (is_mixed_mvs vl1) eqn:MIXED.
  { destruct (classic (chunk = Mint64 \/ chunk = Many64)).
    2:{ do 2 (rewrite chunk_normalize_mvs64; eauto). exploit (decode_val_inject f vl1 vl2 chunk); eauto. }
    rename H into CHUNK.
    assert (MIXED': is_mixed_mvs vl2 = true).
    { rewrite <- MIXED. symmetry. eapply mix_inject_mix; eauto. }
    replace (normalize_mvs chunk m1 vl1) with (map (_decode_normalize_mv m1) vl1).
    2:{ unfold normalize_mvs, normalize_check; rewrite MIXED; des_ifs; des; clarify. }
    replace (normalize_mvs chunk m2 vl2) with (map (_decode_normalize_mv m2) vl2).
    2:{ unfold normalize_mvs, normalize_check; rewrite MIXED'; des_ifs; des; clarify. }
    destruct (proj_bytes (map (_decode_normalize_mv m1) vl1)) eqn:BYTES1.
    { assert (BYTES2: proj_bytes (map (_decode_normalize_mv m2) vl2) = Some l).
      { clear - MVINJ CONC MIXED MIXED' BYTES1. eapply mixed_ptrlikes in MIXED, MIXED'. des.
        ginduction MVINJ; ss; i; clarify. des_ifs_safe. eapply andb_prop in MIXED, MIXED'. des.
        exploit IHMVINJ; eauto. i. rewrite H0.
        (* need lemma : src normalize to byte -> tgt too *)
        assert (_decode_normalize_mv m2 b1 = Byte i).
        { inv H; ss. des_ifs_safe. dup H1. inv H1; ss.
          - clarify. ss. rewrite Heq2. ss.
          - des_ifs_safe. ss. unfold ptr2int in *. des_ifs_safe. erewrite CONC; eauto.
            2:{ eapply concrete_valid. eauto. }
            ss. replace (Int64.repr (z0 - delta + Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta))))
              with (Int64.repr (z0 + Ptrofs.unsigned ofs1)).
            2:{ eapply Int64.same_if_eq. unfold Int64.eq. do 2 rewrite Int64.unsigned_repr_eq. des_ifs.
                exfalso. eapply n0. rewrite <- Ptrofs.modulus_eq64; eauto.
                unfold Ptrofs.add. repeat rewrite Int64.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
                rewrite (Zplus_mod_idemp_r delta). rewrite Zplus_mod_idemp_r.
                f_equal. lia. }
            rewrite Heq2. ss. }
        rewrite H1. auto. }
      unfold decode_val. rewrite BYTES1, BYTES2. des_ifs; econs. }
    assert (UNDEF: decode_val chunk (map (_decode_normalize_mv m1) vl1) = Vundef).
    { (* need lemma : vl mixed -> vl normalize mixed *)
      assert (MIXED'': is_mixed_mvs (map (_decode_normalize_mv m1) vl1) = true).
      { clear - BYTES1 MIXED.
        unfold is_mixed_mvs. repeat rewrite andb_true_iff. splits.
        - eapply mixed_ptrlikes in MIXED. clear BYTES1. des.
          rewrite forallb_forall in *. i. exploit list_in_map_inv; eauto. i. des.
          subst. exploit MIXED; eauto. i. destruct x0; ss. des_ifs. destruct v; ss; clarify.
          + ss. eapply nth_error_In in Heq0. exploit (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned i))).
            { rewrite encode_int_length. lia. }
            unfold rev_if_be_mv in Heq0. des_ifs. rewrite <- in_rev in Heq0.
            i. des. rewrite forallb_forall in H2. eapply H2 in Heq0. destruct m; ss.
          + des_ifs. ss. eapply nth_error_In in Heq0.
            unfold rev_if_be_mv in Heq0. des_ifs. rewrite <- in_rev in Heq0.
            exploit (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned (Int64.repr z)))).
            { rewrite encode_int_length. lia. }
            i. des. rewrite forallb_forall in H2. eapply H2 in Heq0. destruct m; ss.
        - destruct (forallb is_ptr_mv (map (_decode_normalize_mv m1) vl1)) eqn:PTR; auto.
          exfalso. unfold is_mixed_mvs in MIXED. repeat rewrite andb_true_iff in MIXED. des.
          rewrite negb_true_iff in MIXED0. erewrite normalize_result_fragments in PTR; clarify.
          rewrite forallb_forall in *. ii. exploit PTR; eauto. i. destruct x; ss. }
      destruct (forallb is_intptr_mv (map (_decode_normalize_mv m1) vl1)) eqn:IP.
      { eapply normalized_intptr_undef; eauto. unfold normalize_check. des_ifs; des; clarify. }
      eapply mixed_decode_val_undefs; eauto. unfold is_mixed_mvs_old, is_mixed_mvs in *.
      rewrite IP. eapply andb_prop in MIXED''. des_safe. ss. clear - BYTES1.
      erewrite not_bytes_proj_bytes_iff in BYTES1. rewrite BYTES1. ss. }
    rewrite UNDEF. econs. }
  assert (MIXED': is_mixed_mvs vl2 = false).
  { rewrite <- MIXED. symmetry. eapply mix_inject_mix; eauto. }
  unfold normalize_mvs, normalize_check. rewrite MIXED, MIXED'.
  exploit (decode_val_inject f vl1 vl2 chunk); eauto. i. destruct chunk; ss.
Qed.

Lemma load_inj:
  forall f m1 m2 chunk b1 ofs b2 delta v1 (CONC: forall b1 b2 delta addr, f b1 = Some (b2, delta) -> valid_block m1 b1 ->
                                                                m1.(mem_concrete)!b1 = Some addr ->
                                                                m2.(mem_concrete)!b2 = Some (addr-delta)),
  mem_inj f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros.
  exists (decode_val chunk (normalize_mvs chunk m2 (getN (size_chunk_nat chunk) (ofs + delta) (m2.(mem_contents)#b2)))).
  split. unfold load. apply pred_dec_true.
  eapply valid_access_inj; eauto with mem.
  exploit load_result; eauto. intro. rewrite H2.
  apply normalize_mvs_decode_val_inject; eauto.
  { rewrite getN_length. unfold size_chunk_nat. destruct chunk; ss; lia. }
  apply getN_inj; auto.
  rewrite <- size_chunk_conv. exploit load_valid_access; eauto. intros [A B]. auto.
Qed.

Lemma loadbytes_inj:
  forall f m1 m2 len b1 ofs b2 delta bytes1,
  mem_inj f m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m1 b1 ofs (ofs + len) Cur Readable); inv H0.
  exists (getN (Z.to_nat len) (ofs + delta) (m2.(mem_contents)#b2)).
  split. apply pred_dec_true.
  replace (ofs + delta + len) with ((ofs + len) + delta) by lia.
  eapply range_perm_inj; eauto with mem.
  apply getN_inj; auto.
  destruct (zle 0 len). rewrite Z2Nat.id by lia. auto.
  rewrite Z_to_nat_neg by lia. simpl. red; intros; extlia.
Qed.

(** Preservation of stores. *)

Lemma setN_inj:
  forall (access: Z -> Prop) delta f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  forall p c1 c2,
  (forall q, access q -> memval_inject f (ZMap.get q c1) (ZMap.get (q + delta) c2)) ->
  (forall q, access q -> memval_inject f (ZMap.get q (setN vl1 p c1))
                                         (ZMap.get (q + delta) (setN vl2 (p + delta) c2))).
Proof.
  induction 1; intros; simpl.
  auto.
  replace (p + delta + 1) with ((p + 1) + delta) by lia.
  apply IHlist_forall2; auto.
  intros. rewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0.
  rewrite ZMap.gss. auto.
  rewrite ZMap.gso. auto. unfold ZIndexed.t in *. lia.
Qed.

Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m b1 ofs1 Max Nonempty ->
  perm m b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Lemma store_mapped_inj:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ mem_inj f n1 n2.
Proof.
  intros.
  assert (valid_access m2 chunk b2 (ofs + delta) Writable).
    eapply valid_access_inj; eauto with mem.
  destruct (valid_access_store _ _ _ _ v2 H4) as [n2 STORE].
  exists n2; split. auto.
  constructor.
(* perm *)
  intros. eapply perm_store_1; [eexact STORE|].
  eapply mi_perm; eauto.
  eapply perm_store_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros; eauto with mem.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite (store_mem_contents _ _ _ _ _ _ STORE).
  rewrite ! PMap.gsspec.
  destruct (peq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite peq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable).
  apply encode_val_inject; auto. intros. eapply mi_memval; eauto. eauto with mem.
  destruct (peq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. eapply mi_memval; eauto. eauto with mem.
  rewrite encode_val_length. rewrite <- size_chunk_conv. intros.
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply H1; eauto. eauto 6 with mem.
    exploit store_valid_access_3. eexact H0. intros [A B].
    eapply perm_implies. apply perm_cur_max. apply A. lia. auto with mem.
  destruct H8. congruence. lia.
  (* block <> b1, block <> b2 *)
  eapply mi_memval; eauto. eauto with mem.
Qed.

Lemma store_unmapped_inj:
  forall f chunk m1 b1 ofs v1 n1 m2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  mem_inj f n1 m2.
Proof.
  intros. constructor.
(* perm *)
  intros. eapply mi_perm; eauto with mem.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros; eauto with mem.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite PMap.gso. eapply mi_memval; eauto with mem.
  congruence.
Qed.

Lemma store_outside_inj:
  forall f m1 m2 chunk b ofs v m2',
  mem_inj f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. inv H. constructor.
(* perm *)
  eauto with mem.
(* access *)
  intros; eapply mi_align0; eauto.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H1).
  rewrite PMap.gsspec. destruct (peq b2 b). subst b2.
  rewrite setN_outside. auto.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (zlt (ofs0 + delta) ofs); auto.
  destruct (zle (ofs + size_chunk chunk) (ofs0 + delta)). lia.
  byContradiction. eapply H0; eauto. lia.
  eauto with mem.
Qed.

Lemma storebytes_mapped_inj:
  forall f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ mem_inj f n1 n2.
Proof.
  intros. inversion H.
  assert (range_perm m2 b2 (ofs + delta) (ofs + delta + Z.of_nat (length bytes2)) Cur Writable).
    replace (ofs + delta + Z.of_nat (length bytes2))
       with ((ofs + Z.of_nat (length bytes1)) + delta).
    eapply range_perm_inj; eauto with mem.
    eapply storebytes_range_perm; eauto.
    rewrite (list_forall2_length H3). lia.
  destruct (range_perm_storebytes _ _ _ _ H4) as [n2 STORE].
  exists n2; split. eauto.
  constructor.
(* perm *)
  intros.
  eapply perm_storebytes_1; [apply STORE |].
  eapply mi_perm0; eauto.
  eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs0 Cur Readable). eapply perm_storebytes_2; eauto.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite (storebytes_mem_contents _ _ _ _ _ STORE).
  rewrite ! PMap.gsspec. destruct (peq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite peq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable); auto.
  destruct (peq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. auto.
  intros.
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply H1; eauto 6 with mem.
    exploit storebytes_range_perm. eexact H0.
    instantiate (1 := r - delta).
    rewrite (list_forall2_length H3). lia.
    eauto 6 with mem.
  destruct H9. congruence. lia.
  (* block <> b1, block <> b2 *)
  eauto.
Qed.

Lemma storebytes_unmapped_inj:
  forall f m1 b1 ofs bytes1 n1 m2,
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  mem_inj f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* perm *)
  intros. eapply mi_perm0; eauto. eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite PMap.gso. eapply mi_memval0; eauto. eapply perm_storebytes_2; eauto.
  congruence.
Qed.

Lemma storebytes_outside_inj:
  forall f m1 m2 b ofs bytes2 m2',
  mem_inj f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z.of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros. eapply perm_storebytes_1; eauto with mem.
(* align *)
  eauto.
(* mem_contents *)
  intros.
  rewrite (storebytes_mem_contents _ _ _ _ _ H1).
  rewrite PMap.gsspec. destruct (peq b2 b). subst b2.
  rewrite setN_outside. auto.
  destruct (zlt (ofs0 + delta) ofs); auto.
  destruct (zle (ofs + Z.of_nat (length bytes2)) (ofs0 + delta)). lia.
  byContradiction. eapply H0; eauto. lia.
  eauto with mem.
Qed.

Lemma storebytes_empty_inj:
  forall f m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  mem_inj f m1' m2'.
Proof.
  intros. destruct H. constructor.
(* perm *)
  intros.
  eapply perm_storebytes_1; eauto.
  eapply mi_perm0; eauto.
  eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs Cur Readable). eapply perm_storebytes_2; eauto.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite (storebytes_mem_contents _ _ _ _ _ H1).
  simpl. rewrite ! PMap.gsspec.
  destruct (peq b0 b1); destruct (peq b3 b2); subst; eapply mi_memval0; eauto.
Qed.

(** Preservation of allocations *)

Lemma alloc_right_inj:
  forall f m1 m2 lo hi b2 m2',
  mem_inj f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  mem_inj f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* perm *)
  intros. eapply perm_alloc_1; eauto.
(* align *)
  eauto.
(* mem_contents *)
  intros.
  assert (perm m2 b0 (ofs + delta) Cur Readable).
    eapply mi_perm0; eauto.
  assert (valid_block m2 b0) by eauto with mem.
  rewrite <- MEM; simpl. rewrite PMap.gso. eauto with mem.
  rewrite NEXT. eauto with mem.
Qed.

Lemma alloc_left_unmapped_inj:
  forall f m1 m2 lo hi m1' b1,
  mem_inj f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  f b1 = None ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros. exploit perm_alloc_inv; eauto. intros.
  destruct (eq_block b0 b1). congruence. eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. exploit perm_alloc_inv; eauto.
  destruct (eq_block b0 b1); auto. congruence.
(* mem_contents *)
  injection H0; intros NEXT MEM. intros.
  rewrite <- MEM; simpl. rewrite NEXT.
  exploit perm_alloc_inv; eauto. intros.
  rewrite PMap.gsspec. unfold eq_block in H4. destruct (peq b0 b1).
  rewrite ZMap.gi. constructor. eauto.
Qed.

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Lemma alloc_left_mapped_inj:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  mem_inj f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  inj_offset_aligned delta (hi-lo) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  f b1 = Some(b2, delta) ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros.
  exploit perm_alloc_inv; eauto. intros. destruct (eq_block b0 b1). subst b0.
  rewrite H4 in H5; inv H5. eauto. eauto.
(* align *)
  intros. destruct (eq_block b0 b1).
  subst b0. assert (delta0 = delta) by congruence. subst delta0.
  assert (lo <= ofs < hi).
  { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); lia. }
  assert (lo <= ofs + size_chunk chunk - 1 < hi).
  { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); lia. }
  apply H2. lia.
  eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. eapply perm_alloc_4; eauto.
(* mem_contents *)
  injection H0; intros NEXT MEM.
  intros. rewrite <- MEM; simpl. rewrite NEXT.
  exploit perm_alloc_inv; eauto. intros.
  rewrite PMap.gsspec. unfold eq_block in H7.
  destruct (peq b0 b1). rewrite ZMap.gi. constructor. eauto.
Qed.

Lemma free_left_inj:
  forall f m1 m2 b lo hi m1',
  mem_inj f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  mem_inj f m1' m2.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H. constructor.
(* perm *)
  intros. eauto with mem.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros; eapply perm_free_3; eauto.
(* mem_contents *)
  intros. rewrite FREE; simpl. eauto with mem.
Qed.

Lemma free_right_inj:
  forall f m1 m2 b lo hi m2',
  mem_inj f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  mem_inj f m1 m2'.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H.
  assert (PERM:
    forall b1 b2 delta ofs k p,
    f b1 = Some (b2, delta) ->
    perm m1 b1 ofs k p -> perm m2' b2 (ofs + delta) k p).
  intros.
  intros. eapply perm_free_1; eauto.
  destruct (eq_block b2 b); auto. subst b. right.
  assert (~ (lo <= ofs + delta < hi)). red; intros; eapply H1; eauto.
  lia.
  constructor.
(* perm *)
  auto.
(* align *)
  eapply mi_align0; eauto.
(* mem_contents *)
  intros. rewrite FREE; simpl. eauto.
Qed.

(** Preservation of [drop_perm] operations. *)

Lemma drop_unmapped_inj:
  forall f m1 m2 b lo hi p m1',
  mem_inj f m1 m2 ->
  drop_perm m1 b lo hi p = Some m1' ->
  f b = None ->
  mem_inj f m1' m2.
Proof.
  intros. inv H. constructor.
(* perm *)
  intros. eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* contents *)
  intros.
  replace (ZMap.get ofs m1'.(mem_contents)#b1) with (ZMap.get ofs m1.(mem_contents)#b1).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in H0; destruct (range_perm_dec m1 b lo hi Cur Freeable); inv H0; auto.
Qed.

Lemma drop_mapped_inj:
  forall f m1 m2 b1 b2 delta lo hi p m1',
  mem_inj f m1 m2 ->
  drop_perm m1 b1 lo hi p = Some m1' ->
  meminj_no_overlap f m1 ->
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
   /\ mem_inj f m1' m2'.
Proof.
  intros.
  assert ({ m2' | drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2' }).
  apply range_perm_drop_2. red; intros.
  replace ofs with ((ofs - delta) + delta) by lia.
  eapply perm_inj; eauto. eapply range_perm_drop_1; eauto. lia.
  destruct X as [m2' DROP]. exists m2'; split; auto.
  inv H.
  constructor.
(* perm *)
  intros.
  assert (perm m2 b3 (ofs + delta0) k p0).
    eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
  destruct (eq_block b1 b0).
  (* b1 = b0 *)
  subst b0. rewrite H2 in H; inv H.
  destruct (zlt (ofs + delta0) (lo + delta0)). eapply perm_drop_3; eauto.
  destruct (zle (hi + delta0) (ofs + delta0)). eapply perm_drop_3; eauto.
  assert (perm_order p p0).
    eapply perm_drop_2.  eexact H0. instantiate (1 := ofs). lia. eauto.
  apply perm_implies with p; auto.
  eapply perm_drop_1. eauto. lia.
  (* b1 <> b0 *)
  eapply perm_drop_3; eauto.
  destruct (eq_block b3 b2); auto.
  destruct (zlt (ofs + delta0) (lo + delta)); auto.
  destruct (zle (hi + delta) (ofs + delta0)); auto.
  exploit H1; eauto.
  instantiate (1 := ofs + delta0 - delta).
  apply perm_cur_max. apply perm_implies with Freeable.
  eapply range_perm_drop_1; eauto. lia. auto with mem.
  eapply perm_drop_4; eauto. eapply perm_max. apply perm_implies with p0. eauto.
  eauto with mem.
  intuition.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* memval *)
  intros.
  replace (m1'.(mem_contents)#b0) with (m1.(mem_contents)#b0).
  replace (m2'.(mem_contents)#b3) with (m2.(mem_contents)#b3).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in DROP; destruct (range_perm_dec m2 b2 (lo + delta) (hi + delta) Cur Freeable); inv DROP; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m1 b1 lo hi Cur Freeable); inv H0; auto.
Qed.

Lemma drop_outside_inj: forall f m1 m2 b lo hi p m2',
  mem_inj f m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs' k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs' k p ->
    lo <= ofs' + delta < hi -> False) ->
  mem_inj f m1 m2'.
Proof.
  intros. inv H. constructor.
  (* perm *)
  intros. eapply perm_drop_3; eauto.
  destruct (eq_block b2 b); auto. subst b2. right.
  destruct (zlt (ofs + delta) lo); auto.
  destruct (zle hi (ofs + delta)); auto.
  byContradiction. exploit H1; eauto. lia.
  (* align *)
  eapply mi_align0; eauto.
  (* contents *)
  intros.
  replace (m2'.(mem_contents)#b2) with (m2.(mem_contents)#b2).
  apply mi_memval0; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m2 b lo hi Cur Freeable); inv H0; auto.
Qed.

(** * Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by increasing the sizes of the memory blocks of [m1] (decreasing
  the low bounds, increasing the high bounds), and replacing some of
  the [Vundef] values stored in [m1] by more defined values stored
  in [m2] at the same locations. *)

Record extends' (m1 m2: mem) : Prop :=
  mk_extends {
    mext_next: nextblock m1 = nextblock m2;
    mext_inj:  mem_inj inject_id m1 m2;
    mext_perm_inv: forall b ofs k p,
      perm m2 b ofs k p ->
      perm m1 b ofs k p \/ ~perm m1 b ofs Max Nonempty;
    mext_concrete: forall b addr,
      valid_block m1 b ->
      m1.(mem_concrete)!b = Some addr ->
      m2.(mem_concrete)!b = Some addr;
  }.

Definition extends := extends'.

Theorem extends_refl:
  forall m, extends m m.
Proof.
  intros. constructor. auto. constructor.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by lia. auto.
  intros. unfold inject_id in H; inv H. apply Z.divide_0_r.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by lia.
  apply memval_lessdef_refl.
  tauto.
  eauto.
Qed.

Theorem valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b).
Proof.
  intros. inv H. unfold valid_block. rewrite mext_next0. tauto.
Qed.

Lemma range_perm_extends m1 m1'
    (MEXT: extends m1 m1')
    b ofs chunk k
    (RPERM: forall o, ofs <= o < ofs + size_chunk chunk ->
              exists p : permission, (mem_access m1) # b o k = Some p) :
  forall o, ofs <= o < ofs + size_chunk chunk ->
    exists p : permission, (mem_access m1') # b o k = Some p.
Proof.
  ii. eapply RPERM in H. des.
  assert (perm m1 b o k p).
  { unfold perm, perm_order'. rewrite H. eapply perm_refl. }
  inv MEXT. eapply mi_perm in H0; eauto.
  2: { unfold inject_id. eauto. }
  rewrite Z.add_0_r in H0. unfold perm, perm_order' in H0.
  des_ifs. eauto.
Qed.

Lemma _weak_valid_pointer_extends m1 m1'
    (MEXT: extends m1 m1')
    b ofs k
    (WVLD: _weak_valid_pointer (mem_access m1) b ofs k) :
  <<WVLD: _weak_valid_pointer (mem_access m1') b ofs k>>.
Proof.
  inv MEXT. inv mext_inj0.
  unfold _weak_valid_pointer, _valid_pointer in *. ss. des.
  - eapply mi_perm0 in WVLD; ss.
    replace (ofs + 0) with ofs in WVLD by lia. eauto.
  - eapply mi_perm0 in WVLD; ss.
    replace ((ofs - 1) + 0) with (ofs - 1) in WVLD by lia. eauto.
Qed.

Lemma capture_extends_backward_aux
      m1 m2 m2' m1' b addr
      (CAPTGT: Mem.capture m1' b addr m2')
      (CAPSRC: Mem.capture m1 b addr m2)
      (MEXT: Mem.extends m1 m1') :
    <<MEXT: Mem.extends m2 m2'>>.
Proof.
  assert (FB: forall b, inject_id b = Some (b, 0)) by auto.
  inv CAPTGT. inv CAPSRC. inv MEXT. inv mext_inj0.
  econs; eauto.
  - rewrite <- NEXTBLOCK, <- NEXTBLOCK0. auto.
  - econs; eauto.
    + i. inv H. unfold perm, perm_order' in H0. des_ifs. ss.
      exploit mi_perm0; try eapply FB; eauto.
      { unfold perm, perm_order'. rewrite ACCESS0, Heq. eauto. }
      i. unfold perm, perm_order' in *. rewrite <- ACCESS. eauto.
    + unfold range_perm, perm. rewrite <- ACCESS0. auto.
    + i. inv H. revert H0.
      unfold perm. rewrite <- ACCESS0. rewrite <- CONTENTS0. rewrite <- CONTENTS. auto.
  - (* perm_inv *)
    i. unfold perm in *. rewrite <- ACCESS0.
    rewrite <- ACCESS in H. eapply mext_perm_inv0 in H. auto.
  - (* src_concrete *)
    destruct ((mem_concrete m1) ! b) eqn:SRC_CAPTURED.
    + i. exploit PREVADDR; eauto. i. des; subst.
      exploit PREVADDR0; eauto. i. des; subst.
      rewrite <- H2. rewrite <- H3 in H0.
      eapply mext_concrete0; eauto.
      unfold valid_block in *. rewrite NEXTBLOCK0. eauto.
    + i.
      destruct (classic (b = b0)); subst.
      * destruct ((mem_concrete m1') ! b0) eqn:CONCTGT.
        { exploit PREVADDR; eauto. i. des; subst.
          rewrite H2 in CONCTGT.
          rewrite CAPTURED0 in H0; eauto.
          rewrite PTree.gss in H0. clarify. }
        rewrite CAPTURED; eauto. rewrite CAPTURED0 in H0; eauto.
        rewrite PTree.gss in *; eauto.
      * rewrite CAPTURED0 in H0; eauto. rewrite PTree.gso in H0; eauto.
        unfold valid_block in H. rewrite <- NEXTBLOCK0 in H.
        exploit mext_concrete0; eauto. i.
        erewrite <- concrete_other; eauto. econs; eauto.    
Qed.

Theorem capture_extends_backward
    m1 m2' m1' b addr
    (CAPTGT: capture m1' b addr m2')
    (MEXT: extends m1 m1') :
  (exists m2, <<CAPSRC: capture m1 b addr m2>> /\ <<MEXT: extends m2 m2'>>).
Proof.
  assert (FB: forall b, inject_id b = Some (b, 0)) by auto.
  inversion CAPTGT. inversion MEXT.
  assert (valid_block m1 b).
  { rewrite (valid_block_extends m1 m1' b); eauto. }
  destruct ((mem_concrete m1) ! b) eqn:SRC_CAPTURED.
  (* already captured *)
  - esplits.
    (* check capture *)
    + exploit mext_concrete0; eauto. i.
      exploit PREVADDR; eauto. i. des. subst.
      econs; eauto; i; clarify.
    (* extends preserved *)
    + econs; eauto.
      * rewrite mext_next0. auto.
      * inv mext_inj0. econs.
        { i. exploit mi_perm0; eauto. i.
          unfold perm in *. rewrite ACCESS in *. auto. }
        { i. exploit mi_align0; eauto. }
        { i. exploit mi_memval0; eauto. i. rewrite CONTENTS in *. auto. }
      * i. unfold perm, perm_order' in H0. des_ifs; auto.
        rewrite <- ACCESS in Heq.
        exploit mext_perm_inv0; eauto.
        { unfold perm. rewrite Heq. eauto. }
      * i. exploit mext_concrete0; try eapply SRC_CAPTURED; eauto. i.
        exploit PREVADDR; eauto. i. des; subst.
        exploit mext_concrete0; try eapply H1; eauto. i.
        rewrite <- H4; eauto.
  (* capture new conc blk *)
  - rename H into VALID0.
    inv mext_inj0.
    assert(NEXT_LOGICAL: forall b' : positive, ~ Plt b' (nextblock m1) -> (PTree.set b addr (mem_concrete m1)) ! b' = None).
    { i. destruct (peq b' b).
      - subst. unfold valid_block in VALID0. exfalso. apply H. auto.
      - exploit PTree.gso. eapply n. i. erewrite H0. eapply (nextblocks_logical m1). eauto. }

    assert (VALID_IN_RANGE: forall (bo : block) (addr0 : Z),
               addr_in_block (PTree.set b addr (mem_concrete m1)) (mem_access m1) addr0 bo ->
               addr0 < Ptrofs.modulus - 1).
    { i. inv H. rewrite PTree.gsspec in CONCRETE. des_ifs.
      (* about b *)
      - exploit m2'.(valid_address_bounded); eauto.
        { econs; ss; des.
          - destruct ((mem_concrete m1') ! b) eqn:CONCTGT.
            + exploit PREVADDR; eauto. i. des; subst.
              rewrite <- H0. eauto.
            + exploit CAPTURED; eauto. i.
              rewrite H. rewrite PTree.gss. auto.
          - rewrite <- ACCESS.
            assert (perm m1 b (addr0-caddr) Max perm0) by (unfold perm; rewrite PERM; apply perm_refl).
            exploit mi_perm0; try eapply FB; eauto. i.
            unfold perm, perm_order' in H0. des_ifs.
            rewrite Z.add_0_r in Heq. eauto.
          - eauto. }
      (* not b1 *)
      - eapply (valid_address_bounded m1). econs; eauto. }

    assert(NO_CONC_OVLP: forall addr0 : Z, uniqueness (addr_in_block (PTree.set b addr (mem_concrete m1)) (mem_access m1) addr0)).
    { i. unfold uniqueness. i.
      assert (AUX: forall a b, (a - b + 0 = a - b)) by (i; lia).
      inv H; inv H0; ss. des. (* inv CAPTGT. *)
      rename x into bx. rename y into bewhy.
      rename caddr into caddrx. rename caddr0 into caddry. ss.
      assert (SRCPERM1: perm m1 bx (addr0 - caddrx) Max perm1) by (unfold perm; rewrite PERM; apply perm_refl).
      exploit mi_perm0. eapply FB. eauto. i.
      assert (TGTPERM1: perm m2' bx (addr0 - caddrx) Max perm1).
      { unfold perm in *. rewrite <- ACCESS. rewrite <- AUX. auto. }
      assert (SRCPERM2: perm m1 bewhy (addr0 - caddry) Max perm0) by (unfold perm; rewrite PERM0; apply perm_refl).
      exploit mi_perm0. eapply FB. eauto. i.
      assert (TGTPERM2: perm m2' bewhy (addr0 - caddry) Max perm0).
      { unfold perm in *. rewrite <- ACCESS. rewrite <- AUX. auto. }
      destruct (classic(bx = b)); destruct (classic(bewhy = b)); subst; auto.
      (* bx = b /\ by <> b *)
      - rewrite AUX in *. rename bewhy into b'.
        rewrite PTree.gss in CONCRETE; eauto. clarify.
        rewrite PTree.gso in CONCRETE0; eauto.
        exploit mext_concrete0; try eapply CONCRETE0; i.
        { eapply NNPP. ii. eapply nextblocks_logical in H1. clarify. }
        destruct ((mem_concrete m1') ! b) eqn:CONCTGT.
        + exploit PREVADDR; eauto. i. des; subst.
          assert (INBLK1: addr_in_block (mem_concrete m1') (mem_access m1') addr0 b).
          { econs; eauto; ss. unfold perm, perm_order' in *. des_ifs; eauto. }
          assert (INBLK2: addr_in_block (mem_concrete m1') (mem_access m1') addr0 b').
          { econs; eauto; ss. unfold perm, perm_order' in *. des_ifs; eauto. }
          exploit (no_concrete_overlap m1'). eapply INBLK1. eapply INBLK2. eauto.
        + exploit CAPTURED; eauto. i.
          assert (INBLK1: addr_in_block (mem_concrete m2') (mem_access m2') addr0 b).
          { econs; ss.
            - rewrite H3. rewrite PTree.gss; eauto.
            - unfold perm, perm_order' in *. des_ifs; eauto.
            - eauto. }
          assert (INBLK2: addr_in_block (mem_concrete m2') (mem_access m2') addr0 b').
          { econs; ss.
            - rewrite H3. rewrite PTree.gso; eauto.
            - unfold perm, perm_order' in *. des_ifs; eauto.
            - eauto. }
          exploit (no_concrete_overlap m2'). eapply INBLK1. eapply INBLK2. eauto.
      (* bx <> b /\ by = b *)
      - rewrite AUX in *. rename bx into b'.
        rewrite PTree.gso in CONCRETE; eauto.
        rewrite PTree.gss in CONCRETE0; eauto. clarify.
        exploit mext_concrete0; try eapply CONCRETE; i.
        { eapply NNPP. ii. eapply nextblocks_logical in H2. clarify. }  
        destruct ((mem_concrete m1') ! b) eqn:CONCTGT.
        + exploit PREVADDR; eauto. i. des; subst.
          assert (INBLK1: addr_in_block (mem_concrete m1') (mem_access m1') addr0 b).
          { econs; eauto; ss. unfold perm, perm_order' in *. des_ifs; eauto. }
          assert (INBLK2: addr_in_block (mem_concrete m1') (mem_access m1') addr0 b').
          { econs; eauto; ss. unfold perm, perm_order' in *. des_ifs; eauto. }
          exploit (no_concrete_overlap m1'). eapply INBLK1. eapply INBLK2. eauto.
        + exploit CAPTURED; eauto. i.
          assert (INBLK1: addr_in_block (mem_concrete m2') (mem_access m2') addr0 b).
          { econs; eauto; ss. rewrite H3. rewrite PTree.gss; eauto. unfold perm, perm_order' in *. des_ifs; eauto. }
          assert (INBLK2: addr_in_block (mem_concrete m2') (mem_access m2') addr0 b').
          { econs; ss.
            - rewrite H3. rewrite PTree.gso; eauto.
            - unfold perm, perm_order' in *. des_ifs; eauto.
            - eauto. }
          exploit (no_concrete_overlap m2'). eapply INBLK1. eapply INBLK2. eauto.
      - rewrite PTree.gso in *; eauto.
        assert (INBLK1: addr_in_block (mem_concrete m1) (mem_access m1) addr0 bx).
        { econs; eauto; ss. }
        assert (INBLK2: addr_in_block (mem_concrete m1) (mem_access m1) addr0 bewhy).
        { econs; eauto; ss. }
        exploit (no_concrete_overlap m1). eapply INBLK1. eapply INBLK2. eauto. }

    assert (CONC_ALIGN: forall b' caddr, (PTree.set b addr (mem_concrete m1)) ! b' = Some caddr ->
                                    forall ofs chunk,
                                      (forall o, ofs <= o < ofs + size_chunk chunk -> perm_order' ((mem_access m1) # b' o Max) Nonempty) ->
                                      (align_chunk chunk | caddr)).
    { ii.
      destruct (peq b' b).
      { subst. rewrite PTree.gss in H; eauto. clarify.
        exploit capture_concrete; eauto. ii. des.
        eapply (concrete_align m2'); eauto.
        instantiate (1:=ofs). ii.
        eapply H0 in H1. rewrite <- ACCESS.
        exploit mi_perm0; try eapply FB; unfold perm; eauto.
        replace (o + 0) with o by lia. eauto. }
      rewrite PTree.gso in H; eauto.
      eapply (concrete_align m1); eauto. }

    assert (WVLD_RANGE: forall b' caddr ofs, (PTree.set b addr (mem_concrete m1)) ! b' = Some caddr -> 0 <= ofs < Ptrofs.modulus ->
                                        _weak_valid_pointer (mem_access m1) b' ofs Max ->
                                        in_range (caddr + ofs) (1, Ptrofs.modulus)).
    { intros. destruct (peq b' b).
      { subst. rewrite PTree.gss in H; eauto. clarify.
        eapply (m2'.(weak_valid_address_range) b); eauto.
        2: { rewrite <- ACCESS. eapply _weak_valid_pointer_extends; eauto. }
        destruct ((mem_concrete m1') ! b) eqn:CONC1'; ss.
        - exploit PREVADDR; eauto. i. des; clarify. rewrite <- H2. eauto.
        - rewrite CAPTURED; eauto. rewrite PTree.gss; eauto. }
      rewrite PTree.gso in H; eauto. eapply m1.(weak_valid_address_range); eauto. }

    remember (mkmem (mem_contents m1) (mem_access m1) (PTree.set b addr (mem_concrete m1))
                (nextblock m1) (access_max m1) (nextblock_noaccess m1) (contents_default m1)
                NEXT_LOGICAL VALID_IN_RANGE NO_CONC_OVLP CONC_ALIGN WVLD_RANGE) as m2.
    exists m2.

    assert (SRCCAP: capture m1 b addr m2).
    { subst. econs; eauto; ss. ii. clarify. }
    esplits; eauto.
    exploit capture_extends_backward_aux.
    { eapply CAPTGT. }
    all: eauto.
Qed.

Lemma capture_extends_backward_progress
    m1 b addr m1' m2
    (MEXT: extends m1 m1')
    (CAPTURE: capture m1 b addr m2) :
  (exists m2' addr', <<CAPTGT: capture m1' b addr' m2'>>) \/ <<OOM: capture_oom m1' b>>.
Proof.
  inv CAPTURE; inv MEXT.
  assert (valid_block m1' b).
  { unfold valid_block in *. rewrite <- mext_next0. auto. }
  destruct (classic (exists m2' addr', capture m1' b addr' m2')).
  - des. left; eauto.
  - right. red. split; eauto.
Qed.

Lemma denormalize_extends m z m' b ofs
    (MEXT: extends m m')
    (DENO: denormalize z m = Some (b, ofs)) :
  <<DENOTGT: denormalize z m' = Some (b, ofs)>>.
Proof.
  assert (FB: forall b, inject_id b = Some (b, 0)) by auto.
  exploit mext_inj; eauto. i.
  eapply denormalize_info in DENO. des.
  eapply ptr2int_to_denormalize_max; try lia.
  - unfold ptr2int. erewrite mext_concrete; eauto. f_equal; lia.
  - eapply mi_perm in PERM; eauto. replace ofs with (ofs + 0) by lia; eauto.
Qed.

Lemma denormalize_valid_access_extends
    m z m' b ofs
    (MEXT: extends m m')
    (DENO: denormalize z m = Some (b, ofs))
    chunk p
    (VA: valid_access m chunk b ofs p) :
  <<DENOTGT: denormalize z m' = Some (b, ofs)>> /\ <<VA: valid_access m' chunk b ofs p>>.
Proof.
  exploit denormalize_extends; eauto. ii. esplit; eauto.
  eapply mext_inj in MEXT. eapply (valid_access_inj inject_id) in VA; ss; eauto.
  replace (ofs + 0) with ofs in VA by lia. eauto.
Qed.

Theorem load_extends:
  forall chunk m1 m2 b ofs v1,
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. inv H. exploit load_inj; eauto.
  { unfold inject_id. ii; clarify. exploit mext_concrete0; eauto. i. rewrite H. f_equal. lia. }
  unfold inject_id; reflexivity.
  intros [v2 [A B]]. exists v2; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  rewrite val_inject_id in B. auto.
Qed.

Theorem load_extends_backward
    chunk m1 m2 b ofs v2
    (MEXT: extends m1 m2)
    (LOADTGT: load chunk m2 b ofs = Some v2) :
  (exists v1, <<LOADSRC: load chunk m1 b ofs = Some v1>> /\ <<VLD: Val.lessdef v1 v2>>)
  \/ (<<LOADFAIL: load chunk m1 b ofs = None>>).
Proof.
  destruct (load chunk m1 b ofs) eqn:LOADSRC; cycle 1.
  { eauto. }
  left. esplits; eauto.
  exploit load_inj; try eapply MEXT; eauto.
  { unfold inject_id. ii; clarify. erewrite mext_concrete; eauto. rewrite H1. f_equal. lia. }
  { unfold inject_id; reflexivity. }
  intros [v2' [A B]].
  replace (ofs + 0) with ofs in A by lia. clarify.
  rewrite val_inject_id in B. auto.
Qed.

Theorem loadv_extends:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. inv H1.
  { unfold loadv, to_ptr in H0. des_ifs.
    - dup H0. unfold load in H0. des_ifs. exploit denormalize_valid_access_extends; eauto.
      { instantiate (1:=Readable). instantiate (1:=chunk). eapply denormalize_info in Heq2; eauto.
        des. rewrite Ptrofs.unsigned_repr in v; try lia. eauto. }
      i. des. unfold loadv, to_ptr. rewrite DENOTGT. des_ifs_safe. eapply load_extends; eauto.
    - ss. eapply load_extends; eauto. }
  unfold loadv in H0. simpl in H0.
  congruence.
Qed.

Theorem loadbytes_extends:
  forall m1 m2 b ofs len bytes1,
  extends m1 m2 ->
  loadbytes m1 b ofs len = Some bytes1 ->
  exists bytes2, loadbytes m2 b ofs len = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2.
Proof.
  intros. inv H.
  replace ofs with (ofs + 0) by lia. eapply loadbytes_inj; eauto.
Qed.

Theorem store_within_extends:
  forall chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto.
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
    rewrite val_inject_id. eauto.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  constructor; auto.
  rewrite (nextblock_store _ _ _ _ _ _ H0).
  rewrite (nextblock_store _ _ _ _ _ _ A).
  auto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_store_1, perm_store_2.
  unfold store in H0. destruct (valid_access_dec m1 chunk b ofs Writable); inversion H0.
  unfold store in A. destruct (valid_access_dec m2 chunk b (ofs+0) Writable); inversion A. simpl. assumption.
Qed.

Theorem store_outside_extends:
  forall chunk m1 m2 b ofs v m2',
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (nextblock_store _ _ _ _ _ _ H0). auto.
  eapply store_outside_inj; eauto.
  unfold inject_id; intros. inv H2. eapply H1; eauto. lia.
  intros. eauto using perm_store_2.
  assert (mem_concrete m2 = mem_concrete m2').
  { unfold store in *. des_ifs. }
  rewrite H2 in *. eauto.
Qed.

Theorem storev_extends:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inv H1.
  { unfold storev in H0. des_ifs.
    - dup H0. unfold store in H0. des_ifs. exploit denormalize_valid_access_extends; eauto.
      i. des. unfold storev. rewrite DENOTGT. eapply store_within_extends; eauto.
    - ss. eapply store_within_extends; eauto. }
  simpl in *.
  congruence.
Qed.

Theorem storebytes_within_extends:
  forall m1 m2 b ofs bytes1 m1' bytes2,
  extends m1 m2 ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 b ofs bytes2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit storebytes_mapped_inj; eauto.
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  constructor; auto.
  rewrite (nextblock_storebytes _ _ _ _ _ H0).
  rewrite (nextblock_storebytes _ _ _ _ _ A).
  auto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_storebytes_1, perm_storebytes_2.
  unfold storebytes in H0. destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes1)) Cur Writable); inversion H0.
  unfold storebytes in A. destruct (range_perm_dec m2 b (ofs + 0) (ofs + 0 + Z.of_nat (length bytes2)) Cur Writable); inversion A.
  simpl. assumption.
Qed.

Theorem storebytes_outside_extends:
  forall m1 m2 b ofs bytes2 m2',
  extends m1 m2 ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z.of_nat (length bytes2) -> False) ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (nextblock_storebytes _ _ _ _ _ H0). auto.
  eapply storebytes_outside_inj; eauto.
  unfold inject_id; intros. inv H2. eapply H1; eauto. lia.
  intros. eauto using perm_storebytes_2.
  assert (mem_concrete m2 = mem_concrete m2').
  { unfold storebytes in *. des_ifs. }
  rewrite <- H2 in *. eauto.
Qed.

Theorem alloc_extends:
  forall m1 m2 lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2'.
Proof.
  intros. inv H.
  case_eq (alloc m2 lo2 hi2); intros m2' b' ALLOC.
  assert (b' = b).
    rewrite (alloc_result _ _ _ _ _ H0).
    rewrite (alloc_result _ _ _ _ _ ALLOC).
    auto.
  subst b'.
  exists m2'; split; auto.
  constructor.
  rewrite (nextblock_alloc _ _ _ _ _ H0).
  rewrite (nextblock_alloc _ _ _ _ _ ALLOC).
  congruence.
  eapply alloc_left_mapped_inj with (m1 := m1) (m2 := m2') (b2 := b) (delta := 0); eauto.
  eapply alloc_right_inj; eauto.
  eauto with mem.
  red. intros. apply Z.divide_0_r.
  intros.
  eapply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto.
  lia.
  intros. eapply perm_alloc_inv in H; eauto.
  generalize (perm_alloc_inv _ _ _ _ _ H0 b0 ofs Max Nonempty); intros PERM.
  destruct (eq_block b0 b).
  subst b0.
  assert (EITHER: lo1 <= ofs < hi1 \/ ~(lo1 <= ofs < hi1)) by lia.
  destruct EITHER.
  left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
  right; tauto.
  exploit mext_perm_inv0; intuition eauto using perm_alloc_1, perm_alloc_4.
  i. exploit concrete_alloc. eapply H0. i.
  exploit concrete_alloc. eapply ALLOC. i.
  rewrite <- H4 in H3. rewrite <- H5. eapply mext_concrete0; eauto.
  exploit valid_block_alloc_inv; try eapply H0; eauto. ii; des; clarify.
  eapply fresh_block_alloc in H0. eapply nextblocks_logical in H0. clarify.
Qed.

Theorem free_left_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  extends m1' m2.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H0). auto.
  eapply free_left_inj; eauto.
  intros. exploit mext_perm_inv0; eauto. intros [A|A].
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto.
  subst b0. right; eapply perm_free_2; eauto.
  intuition eauto using perm_free_3.
  ii. exploit concrete_free; eauto. i.
  rewrite <- H2 in H1.
  eapply mext_concrete0; eauto.
  exploit nextblock_free; eauto. i. unfold valid_block in *. rewrite <- H3; eauto.
Qed.

Theorem free_right_extends:
  forall m1 m2 b lo hi m2',
  extends m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2'.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H0). auto.
  eapply free_right_inj; eauto.
  unfold inject_id; intros. inv H. eapply H1; eauto. lia.
  intros. eauto using perm_free_3.
  ii. exploit concrete_free; eauto. i.
  rewrite <- H3.
  eapply mext_concrete0; eauto.
Qed.

Theorem free_parallel_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  exists m2',
     free m2 b lo hi = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  assert ({ m2': mem | free m2 b lo hi = Some m2' }).
    apply range_perm_free. red; intros.
    replace ofs with (ofs + 0) by lia.
    eapply perm_inj with (b1 := b); eauto.
    eapply free_range_perm; eauto.
  destruct X as [m2' FREE]. exists m2'; split; auto.
  constructor.
  rewrite (nextblock_free _ _ _ _ _ H0).
  rewrite (nextblock_free _ _ _ _ _ FREE). auto.
  eapply free_right_inj with (m1 := m1'); eauto.
  eapply free_left_inj; eauto.
  unfold inject_id; intros. inv H1.
  eapply perm_free_2. eexact H0. instantiate (1 := ofs); lia. eauto.
  intros. exploit mext_perm_inv0; eauto using perm_free_3. intros [A|A].
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto.
  subst b0. right; eapply perm_free_2; eauto.
  right; intuition eauto using perm_free_3.
  ii. exploit concrete_free. eapply H0. i.
  exploit concrete_free. eapply FREE. i.
  rewrite <- H4. rewrite <- H3 in H2. eapply mext_concrete0; eauto.
  exploit nextblock_free; try eapply H0; eauto. i. unfold valid_block in *. rewrite <- H5; eauto.
Qed.

Theorem perm_extends:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m1 b ofs k p -> perm m2 b ofs k p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by lia.
  eapply perm_inj; eauto.
Qed.

Theorem perm_extends_inv:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m2 b ofs k p -> perm m1 b ofs k p \/ ~perm m1 b ofs Max Nonempty.
Proof.
  intros. inv H; eauto.
Qed.

Theorem valid_access_extends:
  forall m1 m2 chunk b ofs p,
  extends m1 m2 -> valid_access m1 chunk b ofs p -> valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by lia.
  eapply valid_access_inj; eauto. auto.
Qed.

Theorem valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true.
Proof.
  intros.
  rewrite valid_pointer_valid_access in *.
  eapply valid_access_extends; eauto.
Qed.

Theorem weak_valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 ->
  weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true.
Proof.
  intros until 1. unfold weak_valid_pointer. rewrite !orb_true_iff.
  intros []; eauto using valid_pointer_extends.
Qed.

Lemma to_ptr_extends m v v' m' v''
    (MEXT: extends m m')
    (LESS: Val.lessdef v v')
    (TOPTR: to_ptr v m = Some v''):
  <<TOPTRTGT: to_ptr v' m' = Some v''>>.
Proof.
  inv LESS; ss. destruct v'; ss. des_ifs.
  { exploit denormalize_extends; try eapply Heq2; eauto. i. des. clarify. }
  exploit denormalize_extends; try eapply Heq1; eauto. i. des. clarify.
Qed.

Lemma to_int_extends m v v' m' v''
    (MEXT: extends m m')
    (LESS: Val.lessdef v v')
    (TOINT: to_int v m = Some v'') :
  <<TOINTTGT: to_int v' m' = Some v''>>.
Proof.
  inv LESS; ss. destruct v'; ss; clarify. unfold ptr2int in *. des_ifs.
  { eapply mext_concrete in MEXT; eauto; clarify.
    eapply NNPP. ii. eapply nextblocks_logical in H. clarify. }
  eapply mext_concrete in MEXT; eauto; clarify.
  eapply NNPP. ii. eapply nextblocks_logical in H. clarify.
Qed.

(** * Memory injections *)

(** A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address;
- unallocated blocks in [m1] must be mapped to [None] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2];
- distinct blocks in [m1] are mapped to non-overlapping sub-blocks in [m2];
- the sizes of [m2]'s blocks are representable with unsigned machine integers;
- pointers that could be represented using unsigned machine integers remain
  representable after the injection.
*)

Record inject' (f: meminj) (m1 m2: mem) : Prop :=
  mk_inject {
    mi_inj:
      mem_inj f m1 m2;
    mi_freeblocks:
      forall b, ~(valid_block m1 b) -> f b = None;
    mi_mappedblocks:
      forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
    mi_no_overlap:
      meminj_no_overlap f m1;
    mi_representable:
      forall b b' delta ofs,
      f b = Some(b', delta) ->
      perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/ perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
      delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned;
    mi_perm_inv:
      forall b1 ofs b2 delta k p,
      f b1 = Some(b2, delta) ->
      perm m2 b2 (ofs + delta) k p ->
      perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty;
    mi_src_concrete_public
      b1 b2 delta addr
      (INJECT: f b1 = Some(b2, delta))
      (CONCRETE: m1.(mem_concrete)!b1 = Some addr):
      m2.(mem_concrete)!b2 = Some (addr-delta);
    mi_src_concrete_private
      b (NOINJECT: f b = None):
      m1.(mem_concrete)!b = None;
  }.
Definition inject := inject'.

Local Hint Resolve mi_mappedblocks: mem.

(** Preservation of access validity and pointer validity *)

Theorem valid_block_inject_1:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m1 b1.
Proof.
  intros. inv H. destruct (plt b1 (nextblock m1)). auto.
  assert (f b1 = None). eapply mi_freeblocks; eauto. congruence.
Qed.

Theorem valid_block_inject_2:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m2 b2.
Proof.
  intros. eapply mi_mappedblocks; eauto.
Qed.

Local Hint Resolve valid_block_inject_1 valid_block_inject_2: mem.

Theorem perm_inject:
  forall f m1 m2 b1 b2 delta ofs k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  perm m1 b1 ofs k p -> perm m2 b2 (ofs + delta) k p.
Proof.
  intros. inv H0. eapply perm_inj; eauto.
Qed.

Theorem perm_inject_inv:
  forall f m1 m2 b1 ofs b2 delta k p,
  inject f m1 m2 ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) k p ->
  perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty.
Proof.
  intros. eapply mi_perm_inv; eauto.
Qed.

Theorem range_perm_inject:
  forall f m1 m2 b1 b2 delta lo hi k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  range_perm m1 b1 lo hi k p -> range_perm m2 b2 (lo + delta) (hi + delta) k p.
Proof.
  intros. inv H0. eapply range_perm_inj; eauto.
Qed.

Theorem valid_access_inject:
  forall f m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. eapply valid_access_inj; eauto. apply mi_inj; auto.
Qed.

Theorem valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros.
  rewrite valid_pointer_valid_access in H1.
  rewrite valid_pointer_valid_access.
  eapply valid_access_inject; eauto.
Qed.

Theorem weak_valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros until 2. unfold weak_valid_pointer. rewrite !orb_true_iff.
  replace (ofs + delta - 1) with ((ofs - 1) + delta) by lia.
  intros []; eauto using valid_pointer_inject.
Qed.

(** The following lemmas establish the absence of machine integer overflow
  during address computations. *)

Lemma address_inject:
  forall f m1 m2 b1 ofs1 b2 delta p,
  inject f m1 m2 ->
  perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros.
  assert (perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty) by eauto with mem.
  exploit mi_representable; eauto. intros [A B].
  assert (0 <= delta <= Ptrofs.max_unsigned).
    generalize (Ptrofs.unsigned_range ofs1). lia.
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; lia.
Qed.

Lemma address_inject':
  forall f m1 m2 chunk b1 ofs1 b2 delta,
  inject f m1 m2 ->
  valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros. destruct H0. eapply address_inject; eauto.
  apply H0. generalize (size_chunk_pos chunk). lia.
Qed.

Theorem weak_valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros. rewrite weak_valid_pointer_spec in H0.
  rewrite ! valid_pointer_nonempty_perm in H0.
  exploit mi_representable; eauto. destruct H0; eauto with mem.
  intros [A B].
  pose proof (Ptrofs.unsigned_range ofs).
  rewrite Ptrofs.unsigned_repr; lia.
Qed.

Theorem valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  eauto using weak_valid_pointer_inject_no_overflow, valid_pointer_implies.
Qed.

Theorem valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Proof.
  intros. inv H1.
  erewrite address_inject'; eauto.
  eapply valid_pointer_inject; eauto.
  rewrite valid_pointer_valid_access in H0. eauto.
Qed.

Theorem weak_valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Proof.
  intros. inv H1.
  exploit weak_valid_pointer_inject; eauto. intros W.
  rewrite weak_valid_pointer_spec in H0.
  rewrite ! valid_pointer_nonempty_perm in H0.
  exploit mi_representable; eauto. destruct H0; eauto with mem.
  intros [A B].
  pose proof (Ptrofs.unsigned_range ofs).
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; auto; lia.
Qed.

Theorem inject_no_overlap:
  forall f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
Proof.
  intros. inv H. eapply mi_no_overlap0; eauto.
Qed.

Theorem different_pointers_inject:
  forall f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject f m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
  Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  intros.
  rewrite valid_pointer_valid_access in H1.
  rewrite valid_pointer_valid_access in H2.
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H1 H3).
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H2 H4).
  inv H1. simpl in H5. inv H2. simpl in H1.
  eapply mi_no_overlap; eauto.
  apply perm_cur_max. apply (H5 (Ptrofs.unsigned ofs1)). lia.
  apply perm_cur_max. apply (H1 (Ptrofs.unsigned ofs2)). lia.
Qed.

Theorem disjoint_or_equal_inject:
  forall f m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
  inject f m m' ->
  f b1 = Some(b1', delta1) ->
  f b2 = Some(b2', delta2) ->
  range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
  range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
  sz > 0 ->
  b1 <> b2 \/ ofs1 = ofs2 \/ ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
  b1' <> b2' \/ ofs1 + delta1 = ofs2 + delta2
             \/ ofs1 + delta1 + sz <= ofs2 + delta2
             \/ ofs2 + delta2 + sz <= ofs1 + delta1.
Proof.
  intros.
  destruct (eq_block b1 b2).
  assert (b1' = b2') by congruence. assert (delta1 = delta2) by congruence. subst.
  destruct H5. congruence. right. destruct H5. left; congruence. right. lia.
  destruct (eq_block b1' b2'); auto. subst. right. right.
  set (i1 := (ofs1 + delta1, ofs1 + delta1 + sz)).
  set (i2 := (ofs2 + delta2, ofs2 + delta2 + sz)).
  change (snd i1 <= fst i2 \/ snd i2 <= fst i1).
  apply Intv.range_disjoint'; simpl; try lia.
  unfold Intv.disjoint, Intv.In; simpl; intros. red; intros.
  exploit mi_no_overlap; eauto.
  instantiate (1 := x - delta1). apply H2. lia.
  instantiate (1 := x - delta2). apply H3. lia.
  intuition.
Qed.

Theorem aligned_area_inject:
  forall f m m' b ofs al sz b' delta,
  inject f m m' ->
  al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
  (al | sz) ->
  range_perm m b ofs (ofs + sz) Cur Nonempty ->
  (al | ofs) ->
  f b = Some(b', delta) ->
  (al | ofs + delta).
Proof.
  intros.
  assert (P: al > 0) by lia.
  assert (Q: Z.abs al <= Z.abs sz). apply Zdivide_bounds; auto. lia.
  rewrite Z.abs_eq in Q; try lia. rewrite Z.abs_eq in Q; try lia.
  assert (R: exists chunk, al = align_chunk chunk /\ al = size_chunk chunk).
    destruct H0. subst; exists Mint8unsigned; auto.
    destruct H0. subst; exists Mint16unsigned; auto.
    destruct H0. subst; exists Mint32; auto.
    subst; exists Mint64; auto.
  destruct R as [chunk [A B]].
  assert (valid_access m chunk b ofs Nonempty).
    split. red; intros; apply H3. lia. congruence.
  exploit valid_access_inject; eauto. intros [C D].
  congruence.
Qed.

Lemma addr_in_block_inject
  f m m'
  (MINJ: inject f m m')
  b b' delta
  (FB: f b = Some (b', delta))
  addr
  (INBLKSRC: addr_in_block (mem_concrete m) (mem_access m) addr b) :
  <<INBLKTGT: addr_in_block (mem_concrete m') (mem_access m') addr b'>>
.
Proof.
  inv INBLKSRC. des.
  exploit mi_src_concrete_public; eauto. ii.
  assert (perm m b (addr-caddr) Max perm0) by (unfold perm; rewrite PERM; apply perm_refl).
  exploit mi_perm; eauto; ii.
  { eapply mi_inj; eauto. }
  econs; eauto.
  { unfold perm, perm_order' in H1. des_ifs.
    replace (addr - (caddr - delta)) with (addr - caddr + delta) by lia. eauto. }
  exploit mi_representable; eauto.
  { left. instantiate (1:=Ptrofs.repr (addr - caddr)).
    erewrite Ptrofs.unsigned_repr; eauto.
    2: { unfold Ptrofs.max_unsigned in *. lia. }
    unfold perm, perm_order'. des_ifs. eapply perm_any_N. }
  ii. des.
  erewrite Ptrofs.unsigned_repr in H4; eauto.
  2: { unfold Ptrofs.max_unsigned in *. lia. }
  unfold Ptrofs.max_unsigned in *. lia.
Qed.

(** Preservation of inject with regards to the capture operation **)

Lemma capture_inject_backward_aux
    m1 m2 m1' m2' f b1 b2 addr delta
    (INJECT: inject f m1 m1')
    (CAPTURE1: capture m1' b2 (addr - delta) m2')
    (CAPTURE2: capture m1 b1 addr m2)
    (FB: f b1 = Some(b2, delta)) :
  inject f m2 m2'.
Proof.
  inversion INJECT. split.
  - inv mi_inj0. inv CAPTURE1. inv CAPTURE2.
    split.
    (* perm *)
    + unfold perm. rewrite <- ACCESS. rewrite <- ACCESS0. auto.
    (* align *)
    + unfold range_perm, perm. rewrite <- ACCESS0. auto.
    (* mem_val *)
    + unfold perm. rewrite <- ACCESS0. rewrite <- CONTENTS0. rewrite <- CONTENTS. auto.
  (* freeblocks *)
  - inv CAPTURE2. unfold valid_block.
    rewrite <- NEXTBLOCK. auto.
  (* mappedblocks *)
  - i. unfold valid_block in *. inversion CAPTURE1. rewrite <- NEXTBLOCK.
    apply mi_mappedblocks0 with (b:= b) (delta:=delta0). auto.
  (* meminj_no_overlap *)
  - unfold meminj_no_overlap in *. intros.
    apply mi_no_overlap0 with (b1:=b0) (b2:=b3); try assumption;
      inv CAPTURE2; unfold perm in *; rewrite ACCESS; auto.
  (* representable *)
  - i. apply mi_representable0 with b b'. auto.
    inv CAPTURE2. unfold perm in *. rewrite ACCESS. auto.
  (* perm_inv *)
  - i. inv CAPTURE2. unfold perm in *. rewrite <- ACCESS.
    apply mi_perm_inv0 with b3 delta0. auto.
    inv CAPTURE1. rewrite ACCESS0. auto.
  (* src_concrete *)
  - inversion CAPTURE1. inversion CAPTURE2. intros bm1 bm2 deltam addrm HM HBM1.
    destruct (Pos.eq_dec bm1 b1); destruct (Pos.eq_dec bm2 b2); subst.
    (* b = bm1, b' = bm2 *)
    + rewrite FB in HM. inv HM.
      destruct ((mem_concrete m1)!b1) eqn:SRC_CAP.
      * exploit PREVADDR; eauto. i. des. rewrite <- H0.
        exploit PREVADDR0; eauto. i. des. rewrite <- H2 in HBM1.
        exploit mi_src_concrete_public0; eauto.
      * destruct ((mem_concrete m1')!b2) eqn:TGT_CAP.
        { exploit PREVADDR; eauto. i. des.
          exploit CAPTURED0; eauto. i. subst. rewrite <- H0.
          rewrite H1 in HBM1. rewrite PTree.gss in HBM1. clarify. }
        exploit CAPTURED0; eauto. i. exploit CAPTURED. eauto. i.
        rewrite H in HBM1. rewrite H0. rewrite PTree.gss in *. clarify.
    (* b = bm1, b' <> bm2 *)
    + rewrite HM in FB. inv FB.
      unfold not in n. exfalso. apply n. auto.
    (* b <> bm1, b' = bm2 *)
    + exploit concrete_other; try eapply n1; eauto. i.
      rewrite HBM1 in H.
      exploit mi_src_concrete_public0; eauto. i.
      exploit PREVADDR; eauto. i. des. rewrite <- H2. auto.
    (* b <> bm1, b' <> bm2 *)
    + exploit concrete_other; try eapply n; eauto. i.
      exploit concrete_other; try eapply n0; eauto. i.
      rewrite <- H0. apply mi_src_concrete_public0 with (b1:=bm1).
      auto. rewrite H. auto.
  (* src private *)
  - i. inversion CAPTURE2. destruct (Pos.eq_dec b b1); subst.
    + rewrite FB in NOINJECT. inv NOINJECT.
    + exploit concrete_other. eapply CAPTURE2. eauto. i. rewrite <- H. apply mi_src_concrete_private0. auto.
Qed.

Theorem capture_inject_backward
    m1 m2' m1' f b1 b2 addr delta
    (INJECT: inject f m1 m1')
    (CAPTURE: capture m1' b2 (addr-delta) m2')
    (FB: f b1 = Some(b2, delta)) :
  exists m2, <<CAPSRC: capture m1 b1 addr m2>> /\ <<MEM: inject f m2 m2'>>.
Proof.
  inversion INJECT. inv mi_inj0. inversion CAPTURE; subst. unfold meminj_no_overlap in *.
  des. exploit valid_block_inject_1; try eapply FB;  eauto. i.
  destruct ((mem_concrete m1) ! b1) eqn:SRC_CAPTURED.
  (* already captured *)
  - exists m1. exploit mi_src_concrete_public0. eapply FB. eapply SRC_CAPTURED. i.
    exploit PREVADDR; eauto. i. des. rewrite Z.sub_cancel_r in H1. symmetry in H1. subst.
    assert (SRCCAP: capture m1 b1 z m1).
    { econs; eauto; i; clarify. }
    split; auto. exploit capture_inject_backward_aux; eauto.
  (* capture new concrete memory in src *)
  - rename H into VALID0.
    assert(NEXT_LOGICAL: forall b : positive, ~ Plt b (nextblock m1) -> (PTree.set b1 addr (mem_concrete m1)) ! b = None).
    { i. destruct (peq b b1).
      subst. unfold valid_block in VALID0. exfalso. apply H. auto.
      exploit PTree.gso. eapply n. i. erewrite H0. eapply (nextblocks_logical m1). eauto. }

    assert (VALID_IN_RANGE: forall bo addr0,
                              addr_in_block (PTree.set b1 addr (mem_concrete m1)) (mem_access m1) addr0 bo ->
                              addr0 < Ptrofs.modulus - 1).
    { i. inv H.
      destruct (peq bo b1).
      (* about b1 *)
      - rewrite e in *. rewrite PTree.gss in CONCRETE. inversion CONCRETE. rewrite <- H0 in *. clear e CONCRETE H0.
        exploit (m2'.(valid_address_bounded) b2 addr0); eauto.
        { econs; ss.
          - destruct ((mem_concrete m1') ! b2) eqn:CPT_TGT.
            + exploit PREVADDR; eauto. i. des. subst. rewrite <- H0. eauto.
            + exploit CAPTURED; eauto. i. rewrite H. rewrite PTree.gss. auto.
          - assert (AUX1: addr0-addr+delta= addr0-(addr-delta)) by lia.
            rewrite <- AUX1. rewrite <- ACCESS. des.
            assert (perm m1 b1 (addr0-addr) Max perm0) by (unfold perm; rewrite PERM; apply perm_refl).
            exploit mi_perm0; try eapply FB; eauto. i.
            unfold perm, perm_order' in H0. des_ifs. eauto.
          - replace (addr0 - (addr - delta)) with (addr0 - addr + delta) by lia.
            destruct PERM as [p PERM].
            exploit mi_representable0; try eapply FB; eauto.
            { instantiate (1:=Ptrofs.repr (addr0 - addr)).
              left. rewrite Ptrofs.unsigned_repr; eauto.
              2: { unfold Ptrofs.max_unsigned. lia. }
              unfold perm. rewrite PERM. ss. eapply perm_any_N. }
            rewrite Ptrofs.unsigned_repr; eauto.
            2: { unfold Ptrofs.max_unsigned in *. lia. }
            unfold Ptrofs.max_unsigned in *. lia. }
      (* not b1 *)
      - eapply (valid_address_bounded m1). econs; eauto.
        erewrite PTree.gso in CONCRETE; auto. }

    assert(NO_CONC_OVLP: forall addr0 : Z, uniqueness (addr_in_block (PTree.set b1 addr (mem_concrete m1)) (mem_access m1) addr0)).
    { i. unfold uniqueness. i.
      destruct (classic(x = b1)); destruct (classic(y = b1)); subst; auto.
      (* y <> = (b1, addr) *)
      - inv H; inv H0; ss. des.
        rename y into b1'.
        destruct (peq b1 b1'); subst; clarify.
        erewrite PTree.gso in CONCRETE0; auto.
        rewrite PTree.gss in CONCRETE.
        destruct (f b1') eqn:FB'; cycle 1.
        { exploit mi_src_concrete_private0; eauto. i. clarify. }
        destruct p as [b2' delta']. clarify.
        assert (SRCPERM1: perm m1 b1 (addr0 - caddr) Max perm1) by (unfold perm; rewrite PERM; apply perm_refl).
        exploit mi_perm0. eapply FB. eauto. i.
        assert (TGTPERM1: perm m2' b2 (addr0 - caddr + delta) Max perm1).
        { unfold perm in *. rewrite <- ACCESS. auto. }
        assert (SRCPERM2: perm m1 b1' (addr0 - caddr0) Max perm0) by (unfold perm; rewrite PERM0; apply perm_refl).
        exploit mi_perm0. eapply FB'. eauto. i.
        assert (TGTPERM2: perm m2' b2' (addr0 - caddr0+delta') Max perm0).
        { unfold perm in *. rewrite <- ACCESS. auto. }
        unfold perm, perm_order' in TGTPERM1, TGTPERM2. des_ifs.
        exploit mi_src_concrete_public0; eauto. i.

        assert (INBLK1: addr_in_block (mem_concrete m2') (mem_access m2') addr0 b2).
        { econs. 
          - destruct ((mem_concrete m1') ! b2) eqn:TGT_CPT.
            + exploit PREVADDR; eauto. i. des. subst. rewrite <- H4. eauto.
            + exploit CAPTURED; eauto. i. rewrite H3. rewrite PTree.gss. auto.
          - assert ((addr0 - caddr + delta) = (addr0 - (caddr - delta))) by lia.
            rewrite <- H3. eauto.
          - exploit mi_representable0; try eapply FB; eauto.
            { instantiate (1 := Ptrofs.repr (addr0 - caddr)).
              rewrite Ptrofs.unsigned_repr; eauto.
              2 :{ unfold Ptrofs.max_unsigned in *. lia. }
              left. eapply perm_implies; eauto. eapply perm_any_N. }
            rewrite Ptrofs.unsigned_repr; eauto.
            2 :{ unfold Ptrofs.max_unsigned in *. lia. }
            unfold Ptrofs.max_unsigned in *. lia. }
        exploit perm_implies; try eapply SRCPERM1; eauto. eapply perm_any_N. i.
        exploit perm_implies; try eapply SRCPERM2; eauto. eapply perm_any_N. i.
        exploit mi_no_overlap0; eauto. unfold perm. i. des; cycle 1.
        (* b2 = b2' *)
        + assert (INBLK2: addr_in_block (mem_concrete m2') (mem_access m2') addr0 b2').
          { destruct (peq b2 b2').
            (* b2 = b2' *)
            - subst. eauto.
            (* b2 <> b2' *)
            - econs.
              + destruct ((mem_concrete m1') ! b2) eqn:TGT_CPT.
                * exploit PREVADDR; eauto. i. des. subst. rewrite <- H7. eauto.
                * exploit CAPTURED; eauto. i. rewrite H6. erewrite PTree.gso; eauto.
              + assert ((addr0 - caddr0 + delta') = (addr0 - (caddr0 - delta'))) by lia.
                rewrite <- H6. eauto.
              + exploit mi_representable0; try eapply FB'; eauto.
                { instantiate (1:= Ptrofs.repr (addr0 - caddr0)).
                  left. rewrite Ptrofs.unsigned_repr; eauto.
                  unfold Ptrofs.max_unsigned in *. lia. }
                rewrite Ptrofs.unsigned_repr; eauto; [unfold Ptrofs.max_unsigned in *; lia|unfold Ptrofs.max_unsigned in *; lia]. }
          exploit (no_concrete_overlap m2'). eapply INBLK1. eapply INBLK2. i. inv H6.
          exploit PREVADDR; eauto. i. des. lia.
        (* b2 <> b2' *)
        + assert (INBLK2: addr_in_block (mem_concrete m2') (mem_access m2') addr0 b2').
          { econs.
            - destruct ((mem_concrete m1') ! b2) eqn:TGT_CPT.
              * exploit PREVADDR; eauto. i. des. subst. rewrite <- H7. eauto.
              * exploit CAPTURED; eauto. i. rewrite H6. erewrite PTree.gso; eauto.
            - assert ((addr0 - caddr0 + delta') = (addr0 - (caddr0 - delta'))) by lia.
              rewrite <- H6. eauto.
            - exploit mi_representable0; try eapply FB'; eauto.
              { instantiate (1:= Ptrofs.repr (addr0 - caddr0)).
                left. rewrite Ptrofs.unsigned_repr; eauto.
                unfold Ptrofs.max_unsigned in *. lia. }
              rewrite Ptrofs.unsigned_repr; eauto.
              unfold Ptrofs.max_unsigned in *. lia.
              unfold Ptrofs.max_unsigned in *. lia. }
          exploit (no_concrete_overlap m2'). eapply INBLK1. eapply INBLK2. i. inv H6. contradiction.
      (* same as upper case *)
      - inv H; inv H0; ss. des. rename x into b1'.
        destruct (peq b1 b1'); subst; clarify.
        erewrite PTree.gso in CONCRETE; auto.
        rewrite PTree.gss in CONCRETE0.
        destruct (f b1') eqn:FB'; cycle 1.
        { exploit mi_src_concrete_private0; eauto. i. clarify. }
        destruct p as [b2' delta'].
        assert (SRCPERM1: perm m1 b1 (addr0 - caddr0) Max perm0) by (unfold perm; rewrite PERM0; apply perm_refl).
        exploit mi_perm0. eapply FB. eauto. i.
        assert (TGTPERM1: perm m2' b2 (addr0 - caddr0 + delta) Max perm0).
        { unfold perm in *. rewrite <- ACCESS. auto. }
        assert (SRCPERM2: perm m1 b1' (addr0 - caddr) Max perm1) by (unfold perm; rewrite PERM; apply perm_refl).
        exploit mi_perm0. eapply FB'. eauto. i.
        assert (TGTPERM2: perm m2' b2' (addr0 - caddr + delta') Max perm1).
        { unfold perm in *. rewrite <- ACCESS. auto. }
        unfold perm, perm_order' in TGTPERM1, TGTPERM2. des_ifs.
        exploit mi_src_concrete_public0; eauto. i.
        exploit perm_implies; try eapply SRCPERM2. eapply perm_any_N. i.
        exploit perm_implies; try eapply SRCPERM1. eapply perm_any_N. i.

        assert (INBLK1: addr_in_block (mem_concrete m2') (mem_access m2') addr0 b2).
        { econs.
          - destruct ((mem_concrete m1') ! b2) eqn:TGT_CPT.
            + exploit PREVADDR; eauto. i. des. subst. rewrite <- H6. eauto.
            + exploit CAPTURED; eauto. i. rewrite H5. rewrite PTree.gss. auto.
          - assert ((addr0 - caddr0 + delta) = (addr0 - (caddr0 - delta))) by lia.
            rewrite <- H5. eauto.
          - exploit mi_representable0; try eapply FB; eauto.
            { instantiate (1:= Ptrofs.repr (addr0 - caddr0)).
              left. rewrite Ptrofs.unsigned_repr; eauto.
              unfold Ptrofs.max_unsigned in *. lia. }
            rewrite Ptrofs.unsigned_repr; eauto; [unfold Ptrofs.max_unsigned in *; lia|unfold Ptrofs.max_unsigned in *; lia]. }
        exploit mi_no_overlap0; eauto. unfold perm. i. des; cycle 1.
        (* b2 = b2' *)
        + assert (INBLK2: addr_in_block (mem_concrete m2') (mem_access m2') addr0 b2').
          { destruct (peq b2 b2').
            (* b2 = b2' *)
            - subst. eauto.
            (* b2 <> b2' *)
            - econs.
              + destruct ((mem_concrete m1') ! b2) eqn:TGT_CPT.
                * exploit PREVADDR; eauto. i. des. subst. rewrite <- H7. eauto.
                * exploit CAPTURED; eauto. i. rewrite H6. erewrite PTree.gso; eauto.
              + assert ((addr0 - caddr + delta') = (addr0 - (caddr - delta'))) by lia.
                rewrite <- H6. eauto.
              + exploit mi_representable0; try eapply FB'; eauto.
                { instantiate (1:= Ptrofs.repr (addr0 - caddr)).
                  left. rewrite Ptrofs.unsigned_repr; eauto.
                  unfold Ptrofs.max_unsigned in *. lia. }
                rewrite Ptrofs.unsigned_repr; eauto; [unfold Ptrofs.max_unsigned in *; lia|unfold Ptrofs.max_unsigned in *; lia]. }
          exploit (no_concrete_overlap m2'). eapply INBLK1. eapply INBLK2. i. inv H6.
          exploit PREVADDR; eauto. i. lia.
        (* b2 <> b2' *)
        + assert (INBLK2: addr_in_block (mem_concrete m2') (mem_access m2') addr0 b2').
          { econs.
            - destruct ((mem_concrete m1') ! b2) eqn:TGT_CPT.
              * exploit PREVADDR; eauto. i. des. subst. rewrite <- H7. eauto.
              * exploit CAPTURED; eauto. i. rewrite H6. erewrite PTree.gso; eauto.
            - assert ((addr0 - caddr + delta') = (addr0 - (caddr - delta'))) by lia.
              rewrite <- H6. eauto.
            - exploit mi_representable0; try eapply FB'; eauto.
              { instantiate (1:= Ptrofs.repr (addr0 - caddr)).
                left. rewrite Ptrofs.unsigned_repr; eauto.
                unfold Ptrofs.max_unsigned in *. lia. }
              rewrite Ptrofs.unsigned_repr; eauto; [unfold Ptrofs.max_unsigned in *; lia|unfold Ptrofs.max_unsigned in *; lia]. }
          exploit (no_concrete_overlap m2'). eapply INBLK1. eapply INBLK2. i. inv H6. contradiction.
      (* x, y <> (b1, addr) *)
      - rename x into bx. rename y into bewhy.
        inv H; inv H0. des. ss.
        destruct (peq bx b1); destruct (peq bewhy b1); subst.
        (* b1 = bx = by *)
        + rewrite PTree.gss in *. clarify.
        (* bx = b1 /\ by <> b1 *)
        + rewrite PTree.gss in CONCRETE. clarify.
        (* bx <> b1 /\ by = b1 *)
        + rewrite PTree.gss in CONCRETE0. clarify.
        (* bx <> b1 /\ by <> b1 *)
        + rewrite PTree.gso in *; eauto.
          assert (INBLK1: addr_in_block (mem_concrete m1) (mem_access m1) addr0 bx) by (econs; eauto).
          assert (INBLK2: addr_in_block (mem_concrete m1) (mem_access m1) addr0 bewhy) by (econs; eauto).
          exploit (no_concrete_overlap m1). eapply INBLK1. eapply INBLK2. auto. }

    assert (CONC_ALIGN: forall b1' caddr, (PTree.set b1 addr (mem_concrete m1)) ! b1' = Some caddr ->
                            forall ofs chunk,
                              (forall o, ofs <= o < ofs + size_chunk chunk -> perm_order' ((mem_access m1) # b1' o Max) Nonempty) ->
                                (align_chunk chunk | caddr)).
      { ii. destruct (peq b1' b1).
        { subst. rewrite PTree.gss in H; eauto. clarify.
          exploit capture_concrete; eauto. ii. des.
          assert (ALIGNTGT: ((align_chunk chunk) | (caddr - delta))).
          { eapply (concrete_align m2') in H; eauto.
            instantiate (1:= (ofs + delta)). ii.
            exploit range_perm_inject; [eauto|eauto| | | ].
            { unfold range_perm. eauto. }
            { instantiate (1:=o). lia. }
            rewrite <- ACCESS. eauto. }
          exploit mi_align0; try eapply FB.
          { unfold range_perm. eapply H0. }
          ii. eapply Z.divide_add_r with (m:= delta) (p:=caddr-delta) in ALIGNTGT; eauto.
          replace (delta + (caddr - delta)) with caddr in ALIGNTGT by lia. eauto. }
        rewrite PTree.gso in H; eauto.
        eapply (concrete_align m1); eauto. }

      assert (WVLD_RANGE: forall b1' caddr ofs, (PTree.set b1 addr (mem_concrete m1)) ! b1' = Some caddr ->
                                           0 <= ofs < Ptrofs.modulus ->
                                           _weak_valid_pointer (mem_access m1) b1' ofs Max ->
                                           in_range (caddr + ofs) (1, Ptrofs.modulus)).
      { intros. destruct (peq b1' b1).
        2:{ subst. rewrite PTree.gso in H; eauto. clarify. eapply m1.(weak_valid_address_range); eauto. }
        subst. rewrite PTree.gss in H; eauto. clarify.
        exploit (weak_valid_address_range m2' b2 (caddr - delta) (ofs + delta)); eauto.
        { destruct ((mem_concrete m1') ! b2) eqn:CONC1'.
          - exploit PREVADDR; eauto. i. des. subst. rewrite <- H2. eauto.
          - rewrite CAPTURED; eauto. rewrite PTree.gss; eauto. }
        { exploit mi_representable0; eauto.
          { instantiate (1:= (Ptrofs.repr ofs)). rewrite Ptrofs.unsigned_repr.
            2: { unfold Ptrofs.max_unsigned in *. lia. }
            unfold _weak_valid_pointer in H1. unfold perm. des; eauto. }
          i. rewrite Ptrofs.unsigned_repr in H; unfold Ptrofs.max_unsigned in *; lia. }
        { rewrite <- ACCESS. unfold _weak_valid_pointer, _valid_pointer in *.
          des; [left; eapply mi_perm0; eauto|right].
          replace (ofs + delta - 1) with ((ofs - 1) + delta) by lia. eapply mi_perm0; eauto. }
        replace (caddr - delta + (ofs + delta)) with (caddr + ofs) by lia. ss. }
          
    remember (mkmem (mem_contents m1) (mem_access m1) (PTree.set b1 addr (mem_concrete m1))
                    (nextblock m1) (access_max m1) (nextblock_noaccess m1) (contents_default m1)
                    NEXT_LOGICAL VALID_IN_RANGE NO_CONC_OVLP CONC_ALIGN WVLD_RANGE) as m2.
    exists m2.
    assert (SRCCAP: capture m1 b1 addr m2).
    { subst. econs; eauto; ss; i. ii. clarify. }
    esplits; auto. exploit capture_inject_backward_aux; eauto.
Qed.

Lemma capture_injects_backward_progress
    m1 b1 addr m1' f m2 b2 delta
    (INJECT: inject f m1 m1')
    (CAPTURE: capture m1 b1 addr m2)
    (FB: f b1 = Some (b2, delta)) :
  (exists m2' addr', <<CAPTGT: capture m1' b2 addr' m2'>>) \/ <<OOM: capture_oom m1' b2>>.
Proof.
  inv CAPTURE; inv INJECT.
  exploit mi_mappedblocks0; eauto. i.
  destruct (classic (exists m2' addr', capture m1' b2 addr' m2')).
  - des. left; eauto.
  - right. ii. split; eauto.
Qed.

Definition ptr_inj (f: meminj) (b b': block) (ofs ofs': Z) :=
  exists delta, f b = Some (b', delta) /\ ofs' = ofs + delta.

Definition ptr_inj_list_exists (f: meminj) (pl pl': list (block * Z)) :=
    forall b o (INSRC: In (b, o) pl),
    exists b' o', <<INTGT: In (b', o') pl'>> /\ <<PINJ: ptr_inj f b b' o o'>>.

Section VAL2PTR.

Variable m1: mem.
Variable m2: mem.
Variable f: meminj.

Hypothesis mi_inj_perm: forall b1 b2 delta ofs k p, f b1 = Some (b2, delta) -> perm m1 b1 ofs k p -> perm m2 b2 (ofs + delta) k p.

Hypothesis src_concrete_private: forall b, f b = None -> (mem_concrete m1) ! b = None.

Hypothesis mappedblocks: forall b b' delta, valid_block m1 b -> f b = Some (b', delta) -> valid_block m2 b'.

Hypothesis src_concrete_public: forall b1 b2 addr delta,
    f b1 = Some (b2, delta) ->
    (mem_concrete m1) ! b1 = Some addr ->
    (mem_concrete m2) ! b2 = Some (addr - delta).

Hypothesis representable: forall b b' delta ofs,
    f b = Some (b', delta) ->
    perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/
    perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
    delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned.

Lemma denormalize_inject_aux
    z b ofs
    (DEMOSRC: denormalize z m1 = Some (b, ofs)) :
  exists b' ofs', 
    <<DENOTGT: denormalize z m2 = Some (b', ofs')>>
  /\ <<VINJ: exists delta, f b = Some (b', delta) /\ ofs' = ofs + delta>>.
Proof.
  unfold denormalize in DEMOSRC.
  eapply PTree.gselectf in DEMOSRC. des.
  unfold denormalize_aux in DEMOSRC0. rewrite DEMOSRC in DEMOSRC0. des_ifs.
  eapply andb_prop in Heq. des. rename Heq into VALIDSRC. rename Heq0 into INBLKSRC.
  assert (f b = None \/ exists b' delta, f b = Some (b', delta)).
  { destruct (f b); eauto. right. destruct p. esplits; eauto. }
  des.
  { exploit src_concrete_private; eauto. i. clarify. }
  exploit src_concrete_public; eauto. i.
  rewrite <- addr_in_block_iff in INBLKSRC.
  assert (VALIDTGT: is_valid m2 b' = true).
  { rewrite <- valid_block_iff_is_valid in *. eauto. }
  assert (INBLKTGT: addr_in_block (mem_concrete m2) (mem_access m2) z b').
  { inv INBLKSRC. des. clarify.
    exploit mi_inj_perm; eauto.
    - unfold perm, perm_order'. rewrite PERM. eapply perm_refl.
    - ii. econs; eauto.
      + unfold perm, perm_order' in H1. des_ifs.
        replace (z - (a - delta)) with (z - a + delta) by lia. eauto.
      + exploit representable; try eapply H; eauto.
        { instantiate (1:= Ptrofs.repr (z - a)).
          left. rewrite Ptrofs.unsigned_repr; eauto.
          2:{ unfold Ptrofs.max_unsigned in *. lia. }
          unfold perm, perm_order'. rewrite PERM. eapply perm_any_N. }
        rewrite Ptrofs.unsigned_repr; eauto.
        { unfold Ptrofs.max_unsigned in *. lia. }
        unfold Ptrofs.max_unsigned in *. lia. }
  destruct (denormalize z m2) eqn:TGT; cycle 1.
  { exfalso. eapply PTree.gselectnf in TGT. eapply TGT. esplits; eauto. ii.
    unfold denormalize_aux in H1. des_ifs. ss.
    rewrite addr_in_block_iff in INBLKTGT. clarify. }
  eapply PTree.gselectf in TGT. des. unfold denormalize_aux in TGT0. des_ifs.
  eapply andb_prop in Heq0. des.
  rewrite <- addr_in_block_iff in Heq1.
  exploit no_concrete_overlap; [eapply Heq1|eapply INBLKTGT|].
  ii. subst. esplits; eauto. ii. clarify. lia.
Qed.

Lemma denormalize_inject' z b ofs
    (DENOSRC: denormalize z m1 = Some (b, ofs)) :
  exists b' ofs', 
    <<DENOTGT: denormalize z m2 = Some (b', ofs')>>
  /\ <<VINJ: Val.inject f (Vptr b (Ptrofs.repr ofs)) (Vptr b' (Ptrofs.repr ofs'))>>.
Proof.
  exploit denormalize_inject_aux; eauto. ii. des.
  esplits; eauto. econs; eauto. rewrite VINJ0. subst.
  exploit representable; eauto.
  { left. instantiate (1:= Ptrofs.repr ofs).
    exploit denormalize_in_range; try eapply DENOSRC. ii. des.
    eapply PTree.gselectf in DENOSRC. des. unfold denormalize_aux in DENOSRC0. des_ifs.
    eapply andb_prop in Heq0. des. unfold addr_is_in_block in *.
    des_ifs. rewrite Ptrofs.unsigned_repr.
    2: { unfold Ptrofs.max_unsigned in *. lia. }
    unfold perm, perm_order'. rewrite Heq. eapply perm_any_N. }
  eapply denormalize_in_range in DENOSRC, DENOTGT. des.
  ii. rewrite Ptrofs.unsigned_repr in H.
  2: { unfold Ptrofs.max_unsigned in *. lia. }
  des. assert (0 <= delta < Ptrofs.modulus) by lia.
  unfold Ptrofs.add. f_equal.
  rewrite Ptrofs.unsigned_repr.
  2: { unfold Ptrofs.max_unsigned in *. lia. }
  rewrite Ptrofs.unsigned_repr; eauto.
  unfold Ptrofs.max_unsigned in *. lia.
Qed.

Lemma to_int_inject'
    v1 v2 (VINJ: Val.inject f v1 v2)
    v1' (TOINT: to_int v1 m1 = Some v1') :
  exists v2', <<TOINTTGT: to_int v2 m2 = Some v2'>> /\ <<VINJ: Val.inject f v1' v2'>>.
Proof.
  inv VINJ; ss.
  { des_ifs. esplits; eauto. }
  { clarify. esplits; eauto. }
  unfold ptr2int in TOINT. destruct ((mem_concrete m1) ! b1) eqn:CONC; cycle 1.
  { inv TOINT. }
  exploit src_concrete_public; eauto. i. destruct Archi.ptr64 eqn:SF.
- inv TOINT. unfold ptr2int. rewrite H0. esplits; eauto.
  assert (Int64.repr (z + Ptrofs.unsigned ofs1)
          = Int64.repr (z - delta + Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))).
  { eapply Int64.same_if_eq. unfold Int64.eq.
    unfold Ptrofs.add. repeat rewrite Int64.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
    repeat (rewrite Ptrofs.modulus_eq64; eauto). rewrite (Zplus_mod_idemp_r delta). rewrite Zplus_mod_idemp_r.
    replace (z - delta + (Ptrofs.unsigned ofs1 + delta)) with (z + Ptrofs.unsigned ofs1) by lia.
    des_ifs; lia. }
  rewrite H1. econs.
- inv TOINT. unfold ptr2int. rewrite H0. esplits; eauto.
  assert (Int.repr (z + Ptrofs.unsigned ofs1)
          = Int.repr (z - delta + Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))).
  { eapply Int.same_if_eq. unfold Int.eq.
    unfold Ptrofs.add. repeat rewrite Int.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
    repeat (rewrite Ptrofs.modulus_eq32; eauto). rewrite (Zplus_mod_idemp_r delta). rewrite Zplus_mod_idemp_r.
    replace (z - delta + (Ptrofs.unsigned ofs1 + delta)) with (z + Ptrofs.unsigned ofs1) by lia.
    des_ifs; lia. }
  rewrite H1. econs.
Qed.

Lemma to_ptr_inject'
    v1 v2 (VINJ: Val.inject f v1 v2)
    v1' (TOPTR: to_ptr v1 m1 = Some v1') :
  exists v2', <<TOPTRTGT: to_ptr v2 m2 = Some v2'>> /\ <<VINJ: Val.inject f v1' v2'>>.
Proof.
  destruct Archi.ptr64 eqn:SF.
- inv VINJ; simpl in *; try rewrite SF in *; simpl in *; try inv TOPTR; cycle 1.
  { esplits; eauto. }
  destruct (Int64.eq i Int64.zero) eqn:EQ.
  { esplits; eauto. inv H0. econs. }
  destruct (denormalize (Int64.unsigned i) m1) eqn:CONC; inv H0.
  destruct p. inv H1. exploit denormalize_inject'; eauto. i. des.
  rewrite DENOTGT. esplits; eauto.
- inv VINJ; simpl in *; try rewrite SF in *; simpl in *; try inv TOPTR; cycle 1.
  { esplits; eauto. }
  destruct (Int.eq i Int.zero) eqn:EQ.
  { esplits; eauto. inv H0. econs. }
  destruct (denormalize (Int.unsigned i) m1) eqn:CONC; inv H0.
  destruct p. inv H1. exploit denormalize_inject'; eauto. i. des.
  rewrite DENOTGT. esplits; eauto.
Qed.

End VAL2PTR.

Lemma to_int_inject
    f m1 m2 (INJ: inject f m1 m2)
    v1 v2 (VINJ: Val.inject f v1 v2)
    v1' (TOINT: to_int v1 m1 = Some v1') :
  exists v2', <<TOINTTGT: to_int v2 m2 = Some v2'>> /\ <<VINJ: Val.inject f v1' v2'>>.
Proof. eapply to_int_inject'; eauto. inv INJ; eauto. Qed.

Lemma denormalize_inject f m1 m2 z b ofs
    (INJ: inject f m1 m2)
    (DENOSRC: denormalize z m1 = Some (b, ofs)) :
  exists b' ofs', 
    <<DENOTGT: denormalize z m2 = Some (b', ofs')>>
  /\ <<VINJ: Val.inject f (Vptr b (Ptrofs.repr ofs)) (Vptr b' (Ptrofs.repr ofs'))>>
.
Proof. inv INJ. inv mi_inj0. eapply denormalize_inject'; eauto. Qed.

Lemma to_ptr_inject
    f m1 m2 (INJ: inject f m1 m2)
    v1 v2 (VINJ: Val.inject f v1 v2)
    v1' (TOPTR: to_ptr v1 m1 = Some v1') :
  exists v2', <<TOPTRTGT: to_ptr v2 m2 = Some v2'>> /\ <<VINJ: Val.inject f v1' v2'>>.
Proof. eapply to_ptr_inject'; eauto; inv INJ; eauto. inv mi_inj0; eauto. Qed.

(** Preservation of loads *)

Theorem load_inject:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  inject f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H. eapply load_inj; eauto.
Qed.

Theorem load_inject_backward
    f m1 m2 chunk b1 ofs b2 delta v2
    (MINJ: inject f m1 m2)
    (LOADTGT: load chunk m2 b2 (ofs + delta) = Some v2)
    (FINJ: f b1 = Some (b2, delta)) :
  (exists v1, <<LOADSRC: load chunk m1 b1 ofs = Some v1>> /\ <<VINJ: Val.inject f v1 v2>>)
  \/ (<<LOADFAIL: load chunk m1 b1 ofs = None>>).
Proof.
  destruct (load chunk m1 b1 ofs) eqn: LOADSRC; eauto.
  esplits; eauto. left. esplits ; eauto.
  exploit load_inj; try eapply MINJ; eauto.
  { i. eapply mi_src_concrete_public; eauto. }
  i. des. clarify.
Qed.

Theorem loadv_inject:
  forall f m1 m2 chunk a1 a2 v1,
  inject f m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  Val.inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  { unfold loadv in H0. des_ifs. exploit to_ptr_inject; try eapply Heq; eauto. i. des. inv VINJ.
    exploit load_inject; eauto. intros [v2 [LOAD INJ]].
    exists v2; split; auto. unfold loadv. des_ifs.
    exploit load_valid_access; try eapply H0. i.
    eapply (valid_access_perm _ _ _ _ Cur) in H1.
    eapply perm_implies in H1; eauto; [|eapply perm_any_N].
    replace (Ptrofs.unsigned (Ptrofs.add i0 (Ptrofs.repr delta)))
      with (Ptrofs.unsigned i0 + delta); eauto.
    symmetry. eapply address_inject'; eauto with mem. }
  unfold loadv in H0. ss.
  exploit load_inject; eauto. intros [v2 [LOAD INJ]].
  exists v2; split; auto. unfold loadv.
  ss.
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
     with (Ptrofs.unsigned ofs1 + delta).
  auto. symmetry. eapply address_inject'; eauto with mem.
Qed.

Theorem loadv_inject_backward
    f m1 m2 chunk a1 a2 v2
    (MINJ: inject f m1 m2)
    (LOADTGT: loadv chunk m2 a2 = Some v2)
    (VINJ: Val.inject f a1 a2) :
  (exists v1, <<LOADSRC: loadv chunk m1 a1 = Some v1>> /\ <<VINJ': Val.inject f v1 v2>>)
  \/ (<<LOADFAIL: loadv chunk m1 a1 = None>>).
Proof.
  destruct (loadv chunk m1 a1) eqn: LOADSRC.
  - left. exploit loadv_inject; eauto. i. des; clarify. esplits; eauto.
  - right. eauto.
Qed.

Theorem loadbytes_inject:
  forall f m1 m2 b1 ofs len b2 delta bytes1,
  inject f m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Proof.
  intros. inv H. eapply loadbytes_inj; eauto.
Qed.

(** Preservation of stores *)

Theorem store_mapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f n1 n2.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. eapply mi_representable; try eassumption.
  destruct H4; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_store_2.
  intuition eauto using perm_store_1, perm_store_2.
(* src concrete *)
  intros.
  assert (SAMECONC2: n2.(mem_concrete) = m2.(mem_concrete)).
  { unfold store in STORE.
    destruct (valid_access_dec m2 chunk b2 (ofs + delta) Writable); inversion STORE.
    reflexivity. }
  assert (SAMECONC1: n1.(mem_concrete) = m1.(mem_concrete)).
  { unfold store in H0.
    destruct (valid_access_dec m1 chunk b1 ofs Writable); inversion H0.
    reflexivity. }
  rewrite SAMECONC2. apply mi_src_concrete_public0 with (b1:=b0).
  assumption. rewrite <- SAMECONC1. assumption.
(* src private *)
  intros. apply concrete_store in H0. rewrite <- H0.
  apply mi_src_concrete_private0; assumption.
Qed.

Theorem store_unmapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* inj *)
  eapply store_unmapped_inj; eauto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. eapply mi_representable; try eassumption.
  destruct H3; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_store_2.
  intuition eauto using perm_store_1, perm_store_2.
(* src concrete *)
  intros.
  assert (SAMECONC1: n1.(mem_concrete) = m1.(mem_concrete)).
  { unfold store in H0. destruct (valid_access_dec m1 chunk b1 ofs Writable); inversion H0. reflexivity. }
  apply mi_src_concrete_public0 with (b1:=b0). assumption. rewrite <- SAMECONC1. assumption.
(* src private *)
  intros. apply concrete_store in H0. rewrite <- H0.
  apply mi_src_concrete_private0; assumption.
Qed.

Theorem store_outside_inject:
  forall f m1 m2 chunk b ofs v m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply store_outside_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  eauto with mem.
(* perm inv *)
  intros. eauto using perm_store_2.
(* src concrete *)
  intros.
  assert (SAMECONC2: m2'.(mem_concrete) = m2.(mem_concrete)).
  { unfold store in H1. destruct (valid_access_dec m2 chunk b ofs Writable); inversion H1. reflexivity. }
  rewrite SAMECONC2. apply mi_src_concrete_public0 with (b1:=b1); assumption.
(* src private *)
  intros. apply concrete_store in H1. apply mi_src_concrete_private0. assumption.
Qed.

Theorem storev_mapped_inject:
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  inject f m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f n1 n2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  { des_ifs. exploit denormalize_inject; eauto. i. des.
    unfold storev. des_ifs. inversion VINJ; subst.
    exploit store_mapped_inject; eauto. i. des.
    exploit store_valid_access_3; try eapply H0. i.
    eapply (valid_access_perm _ _ _ _ Cur) in H4.
    eapply perm_implies in H4; eauto; [|eapply perm_any_N].
    eapply denormalize_in_range in Heq0, Heq1.
    exploit mi_representable; try eapply H; eauto.
    { instantiate (1:=Ptrofs.repr z).
      left. eapply perm_cur_max.
      rewrite Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; [eauto|des; lia]. }
    i. assert (ofs' = z + delta).
    { rewrite Ptrofs.add_unsigned in H7. des.
      do 2 rewrite Ptrofs.unsigned_repr in *; unfold Ptrofs.max_unsigned in *; try lia.
      assert (Ptrofs.unsigned (Ptrofs.repr ofs') = Ptrofs.unsigned (Ptrofs.repr (z + delta))).
      { rewrite H7. eauto. }
      do 2 rewrite Ptrofs.unsigned_repr in *; unfold Ptrofs.max_unsigned in *; try lia. }
    rewrite H8. eauto. }
  unfold storev.
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
    with (Ptrofs.unsigned ofs1 + delta).
  eapply store_mapped_inject; eauto.
  symmetry. eapply address_inject'; eauto with mem.
Qed.

Theorem storebytes_mapped_inject:
  forall f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ inject f n1 n2.
Proof.
  intros. inversion H.
  exploit storebytes_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H3; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. eapply mi_representable0; eauto.
  destruct H4; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_storebytes_2.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
(* src concrete *)
  intros.
  assert (SAMECONC2: n2.(mem_concrete) = m2.(mem_concrete)).
  { unfold storebytes in STORE. destruct (range_perm_dec m2 b2 (ofs + delta) (ofs + delta + Z.of_nat (length bytes2)) Cur Writable); inversion STORE. reflexivity. }
  assert (SAMECONC1: n1.(mem_concrete) = m1.(mem_concrete)).
  { unfold storebytes in H0.
    destruct (range_perm_dec m1 b1 ofs (ofs + Z.of_nat (length bytes1)) Cur Writable); inversion H0. reflexivity. }
  rewrite SAMECONC2. apply mi_src_concrete_public0 with (b1:=b0). assumption. rewrite <- SAMECONC1. assumption.
(* src private *)
  intros. apply concrete_storebytes in H0. rewrite <- H0.
  apply mi_src_concrete_private0. assumption.
Qed.

Theorem storebytes_unmapped_inject:
  forall f m1 b1 ofs bytes1 n1 m2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* inj *)
  eapply storebytes_unmapped_inj; eauto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. eapply mi_representable0; eauto.
  destruct H3; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
(* src concrete *)
  intros.
  assert (SAMECONC1: n1.(mem_concrete) = m1.(mem_concrete)).
  { unfold storebytes in H0.
    destruct (range_perm_dec m1 b1 ofs (ofs + Z.of_nat (length bytes1)) Cur Writable); inversion H0. reflexivity. }
  apply mi_src_concrete_public0 with (b1:=b0). assumption. rewrite <- SAMECONC1. assumption.
  intros. apply concrete_storebytes in H0. rewrite <- H0.
  apply mi_src_concrete_private0. assumption.
Qed.

Theorem storebytes_outside_inject:
  forall f m1 m2 b ofs bytes2 m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z.of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply storebytes_outside_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eapply mi_perm_inv0; eauto using perm_storebytes_2.
(* src concrete *)
  intros.
  assert (SAMECONC2: m2'.(mem_concrete) = m2.(mem_concrete)).
  { unfold storebytes in H1. destruct (range_perm_dec m2 b ofs (ofs + Z.of_nat (length bytes2)) Cur Writable); inversion H1. reflexivity. }
  rewrite SAMECONC2. apply mi_src_concrete_public0 with (b1:=b1); assumption.
(* src private *)
  intros. apply mi_src_concrete_private0; assumption.
Qed.

Theorem storebytes_empty_inject:
  forall f m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  inject f m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  inject f m1' m2'.
Proof.
  intros. inversion H. constructor; intros.
(* inj *)
  eapply storebytes_empty_inj; eauto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. eapply mi_representable0; eauto.
  destruct H3; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_storebytes_2.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
(* src concrete *)
  intros.
  assert (SAMECONC2: m2'.(mem_concrete) = m2.(mem_concrete)).
  { unfold storebytes in H1. destruct (range_perm_dec m2 b2 ofs2 (ofs2 + Z.of_nat (length nil)) Cur Writable); inversion H1. reflexivity. }
  assert (SAMECONC1: m1'.(mem_concrete) = m1.(mem_concrete)).
  { unfold storebytes in H0.
    destruct (range_perm_dec m1 b1 ofs1 (ofs1 + Z.of_nat (length nil)) Cur Writable); inversion H0. reflexivity. }
  rewrite SAMECONC2. apply mi_src_concrete_public0 with (b1:=b0). assumption. rewrite <- SAMECONC1. assumption.
(* src private *)
  intros. apply concrete_storebytes in H0. rewrite <- H0.
  apply mi_src_concrete_private0. assumption.
Qed.

(* Preservation of allocations *)

Theorem alloc_right_inject:
  forall f m1 m2 lo hi b2 m2',
  inject f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  inject f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* inj *)
  eapply alloc_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eapply perm_alloc_inv in H2; eauto. destruct (eq_block b0 b2).
  subst b0. eelim fresh_block_alloc; eauto.
  eapply mi_perm_inv0; eauto.
(* src concrete *)
  intros.
  assert (SAMECONC2: m2'.(mem_concrete) = m2.(mem_concrete)).
  { unfold alloc in H0. inversion H0. reflexivity. }
  rewrite SAMECONC2. apply mi_src_concrete_public0 with (b1:=b1); assumption.
(* src private *)
  intros. apply mi_src_concrete_private0. assumption.
Qed.

Theorem alloc_left_unmapped_inject:
  forall f m1 m2 lo hi m1' b1,
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then None else f b).
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj f' m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence.
    apply memval_inject_incr with f; auto.
  exists f'; split. constructor.
(* inj *)
  eapply alloc_left_unmapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  intros. unfold f'. destruct (eq_block b b1). auto.
  apply mi_freeblocks0. red; intro; elim H3. eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* no overlap *)
  unfold f'; red; intros.
  destruct (eq_block b0 b1); destruct (eq_block b2 b1); try congruence.
  eapply mi_no_overlap0. eexact H3. eauto. eauto.
  exploit perm_alloc_inv. eauto. eexact H6. rewrite dec_eq_false; auto.
  exploit perm_alloc_inv. eauto. eexact H7. rewrite dec_eq_false; auto.
(* representable *)
  unfold f'; intros.
  destruct (eq_block b b1); try discriminate.
  eapply mi_representable0; try eassumption.
  destruct H4; eauto using perm_alloc_4.
(* perm inv *)
  intros. unfold f' in H3; destruct (eq_block b0 b1); try discriminate.
  exploit mi_perm_inv0; eauto.
  intuition eauto using perm_alloc_1, perm_alloc_4.
(* src concrete *)
  { intros.
    apply mi_src_concrete_public0 with (b1:=b0).
    unfold f' in INJECT.
    destruct (eq_block b0 b1).
    - inversion INJECT.
    - assumption.
    - assert (CONC: m1.(mem_concrete) = m1'.(mem_concrete)).
      { unfold alloc in H0. inversion H0 as [[H3 H4]]. reflexivity. }
      rewrite CONC. assumption. }
(* src private *)
  { intros. unfold f' in NOINJECT. destruct (eq_block b b1).
    + rewrite e in *.
      rewrite <- concrete_alloc with (lo:=lo) (hi:=hi) (m2:=m1') (b:=b1) (m1:=m1).
      apply alloc_result in H0. rewrite H0 in *. apply logical_nextblock. assumption.
    + apply concrete_alloc in H0. rewrite <- H0.
      apply mi_src_concrete_private0. assumption. }
(* incr *)
  split. auto.
(* image *)
  split. unfold f'; apply dec_eq_true.
(* incr *)
  intros; unfold f'; apply dec_eq_false; auto.
Qed.

Theorem alloc_left_mapped_inject:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  0 <= delta <= Ptrofs.max_unsigned ->
  (forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then Some(b2, delta) else f b).
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj f' m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0).
      eapply perm_valid_block with (ofs := ofs). apply H9. generalize (size_chunk_pos chunk); lia.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      apply memval_inject_incr with f; auto.
  exists f'. split. constructor.
(* inj *)
  eapply alloc_left_mapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  unfold f'; intros. destruct (eq_block b b1). subst b.
  elim H9. eauto with mem.
  eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* overlap *)
  unfold f'; red; intros.
  exploit perm_alloc_inv. eauto. eexact H12. intros P1.
  exploit perm_alloc_inv. eauto. eexact H13. intros P2.
  destruct (eq_block b0 b1); destruct (eq_block b3 b1).
  congruence.
  inversion H10; subst b0 b1' delta1.
    destruct (eq_block b2 b2'); auto. subst b2'. right; red; intros.
    eapply H6; eauto. lia.
  inversion H11; subst b3 b2' delta2.
    destruct (eq_block b1' b2); auto. subst b1'. right; red; intros.
    eapply H6; eauto. lia.
  eauto.
(* representable *)
  unfold f'; intros.
  destruct (eq_block b b1).
   subst. injection H9; intros; subst b' delta0. destruct H10.
    exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
    exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
    generalize (Ptrofs.unsigned_range_2 ofs). lia.
   exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
   exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
   generalize (Ptrofs.unsigned_range_2 ofs). lia.
  eapply mi_representable0; try eassumption.
  destruct H10; eauto using perm_alloc_4.
(* perm inv *)
  intros. unfold f' in H9; destruct (eq_block b0 b1).
  inversion H9; clear H9; subst b0 b3 delta0.
  assert (EITHER: lo <= ofs < hi \/ ~(lo <= ofs < hi)) by lia.
  destruct EITHER.
  left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
  right; intros A. eapply perm_alloc_inv in A; eauto. rewrite dec_eq_true in A. tauto.
  exploit mi_perm_inv0; eauto. intuition eauto using perm_alloc_1, perm_alloc_4.
(* src concrete *)
  intros b0 b3 delta0 addr HF' CONC1.
  clear mi_freeblocks0 mi_mappedblocks0 mi_no_overlap0 mi_representable0 mi_perm_inv0.
    assert (HCONC: m1.(mem_concrete) = m1'.(mem_concrete)).
  { unfold alloc in H0. inversion H0 as [[FST SND]]. reflexivity. }
  assert (nextblock: m1.(nextblock) = b1).
  { unfold alloc in H0. inversion H0 as [[FST SND]]. reflexivity. }
  apply mi_src_concrete_public0 with (b1:=b0).
  unfold f' in HF'.
  destruct (eq_block b0 b1); inversion HF'. rewrite <- H10.
  rewrite e in *. clear e.
  rewrite <- HCONC in CONC1.  rewrite <- nextblock in CONC1.
  rewrite logical_nextblock in CONC1. inversion CONC1. reflexivity.
  rewrite HCONC. assumption.
(* src private *)
  intros. apply concrete_alloc in H0. rewrite <- H0.
  apply mi_src_concrete_private0. unfold f' in NOINJECT.
  destruct (eq_block b b1); try assumption. inversion NOINJECT.
(* incr *)
  split. auto.
(* image of b1 *)
  split. unfold f'; apply dec_eq_true.
(* image of others *)
  intros. unfold f'; apply dec_eq_false; auto.
Qed.

Theorem alloc_parallel_inject:
  forall f m1 m2 lo1 hi1 m1' b1 lo2 hi2,
  inject f m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists f', exists m2', exists b2,
  alloc m2 lo2 hi2 = (m2', b2)
  /\ inject f' m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros.
  case_eq (alloc m2 lo2 hi2). intros m2' b2 ALLOC.
  exploit alloc_left_mapped_inject.
  eapply alloc_right_inject; eauto.
  eauto.
  instantiate (1 := b2). eauto with mem.
  instantiate (1 := 0). unfold Ptrofs.max_unsigned. generalize Ptrofs.modulus_pos; lia.
  auto.
  intros. apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. lia.
  red; intros. apply Z.divide_0_r.
  intros. apply (valid_not_valid_diff m2 b2 b2); eauto with mem.
  intros [f' [A [B [C D]]]].
  exists f'; exists m2'; exists b2; auto.
Qed.

(** Preservation of [free] operations *)

Lemma free_left_inject:
  forall f m1 m2 b lo hi m1',
  inject f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  inject f m1' m2.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply free_left_inj; eauto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  auto.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. eapply mi_representable0; try eassumption.
  destruct H2; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto. intuition eauto using perm_free_3.
  eapply perm_free_inv in H4; eauto. destruct H4 as [[A B] | A]; auto.
  subst b1. right; eapply perm_free_2; eauto.
(* src concrete *)
  intros.
  assert (SAMECONC1: m1'.(mem_concrete) = m1.(mem_concrete)).
  { unfold free, unchecked_free in H0. destruct (range_perm_dec m1 b lo hi Cur Freeable); inversion H0. reflexivity. }
  apply mi_src_concrete_public0 with (b1:=b1). assumption. rewrite <- SAMECONC1. assumption.
(* src private *)
  intros. apply concrete_free in H0. rewrite <- H0.
  apply mi_src_concrete_private0. assumption.
Qed.

Lemma free_list_left_inject:
  forall f m2 l m1 m1',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  inject f m1' m2.
Proof.
  induction l; simpl; intros.
  inv H0. auto.
  destruct a as [[b lo] hi].
  destruct (free m1 b lo hi) as [m11|] eqn:E; try discriminate.
  apply IHl with m11; auto. eapply free_left_inject; eauto.
Qed.

Lemma free_right_inject:
  forall f m1 m2 b lo hi m2',
  inject f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi -> False) ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply free_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eauto using perm_free_3.
(* src concrete *)
  intros.
  assert (SAMECONC2: m2'.(mem_concrete) = m2.(mem_concrete)).
  { unfold free, unchecked_free in H0. destruct (range_perm_dec m2 b lo hi Cur Freeable); inversion H0. reflexivity. }
  rewrite SAMECONC2. apply mi_src_concrete_public0 with (b1:=b1); assumption.
(* src private *)
  intros. apply mi_src_concrete_private0. assumption.
Qed.

Lemma perm_free_list:
  forall l m m' b ofs k p,
  free_list m l = Some m' ->
  perm m' b ofs k p ->
  perm m b ofs k p /\
  (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).
Proof.
  induction l; simpl; intros.
  inv H. auto.
  destruct a as [[b1 lo1] hi1].
  destruct (free m b1 lo1 hi1) as [m1|] eqn:E; try discriminate.
  exploit IHl; eauto. intros [A B].
  split. eauto with mem.
  intros. destruct H1. inv H1.
  elim (perm_free_2 _ _ _ _ _ E ofs k p). auto. auto.
  eauto.
Qed.

Theorem free_inject:
  forall f m1 l m1' m2 b lo hi m2',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) ->
    perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f m1' m2'.
Proof.
  intros.
  eapply free_right_inject; eauto.
  eapply free_list_left_inject; eauto.
  intros. exploit perm_free_list; eauto. intros [A B].
  exploit H2; eauto. intros [lo1 [hi1 [C D]]]. eauto.
Qed.

Theorem free_parallel_inject:
  forall f m1 m2 b lo hi m1' b' delta,
  inject f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  f b = Some(b', delta) ->
  exists m2',
     free m2 b' (lo + delta) (hi + delta) = Some m2'
  /\ inject f m1' m2'.
Proof.
  intros.
  destruct (range_perm_free m2 b' (lo + delta) (hi + delta)) as [m2' FREE].
  eapply range_perm_inject; eauto. eapply free_range_perm; eauto.
  exists m2'; split; auto.
  eapply free_inject with (m1 := m1) (l := (b,lo,hi)::nil); eauto.
  simpl; rewrite H0; auto.
  intros. destruct (eq_block b1 b).
  subst b1. rewrite H1 in H2; inv H2.
  exists lo, hi; split; auto with coqlib. lia.
  exploit mi_no_overlap. eexact H. eexact n. eauto. eauto.
  eapply perm_max. eapply perm_implies. eauto. auto with mem.
  instantiate (1 := ofs + delta0 - delta).
  apply perm_cur_max. apply perm_implies with Freeable; auto with mem.
  eapply free_range_perm; eauto. lia.
  intros [A|A]. congruence. lia.
Qed.

Lemma drop_outside_inject: forall f m1 m2 b lo hi p m2',
  inject f m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  inject f m1 m2'.
Proof.
  intros. destruct H. constructor; eauto.
  eapply drop_outside_inj; eauto.
  intros. unfold valid_block in *. erewrite nextblock_drop; eauto.
  intros. eapply mi_perm_inv0; eauto using perm_drop_4.
(* src concrete *)
  intros.
  assert (SAMECONC2: m2'.(mem_concrete) = m2.(mem_concrete)).
  { unfold drop_perm in H0. destruct (range_perm_dec m2 b lo hi Cur Freeable); inversion H0. reflexivity. }
  rewrite SAMECONC2. apply mi_src_concrete_public0 with (b1:=b1); assumption.  
Qed.

(** Composing two memory injections. *)

Lemma mem_inj_compose:
  forall f f' m1 m2 m3,
  mem_inj f m1 m2 -> mem_inj f' m2 m3 -> mem_inj (compose_meminj f f') m1 m3.
Proof.
  intros. unfold compose_meminj. inv H; inv H0; constructor; intros.
  (* perm *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by lia.
  eauto.
  (* align *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
  apply Z.divide_add_r.
  eapply mi_align0; eauto.
  eapply mi_align1 with (ofs := ofs + delta') (p := p); eauto.
  red; intros. replace ofs0 with ((ofs0 - delta') + delta') by lia.
  eapply mi_perm0; eauto. apply H0. lia.
  (* memval *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by lia.
  eapply memval_inject_compose; eauto.
Qed.

Theorem inject_compose:
  forall f f' m1 m2 m3,
  inject f m1 m2 -> inject f' m2 m3 ->
  inject (compose_meminj f f') m1 m3.
Proof.
  unfold compose_meminj; intros.
  inv H; inv H0. constructor.
(* inj *)
  eapply mem_inj_compose; eauto.
(* unmapped *)
  intros. erewrite mi_freeblocks0; eauto.
(* mapped *)
  intros.
  destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate.
  destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H.
  eauto.
(* no overlap *)
  red; intros.
  destruct (f b1) as [[b1x delta1x] |] eqn:?; try discriminate.
  destruct (f' b1x) as [[b1y delta1y] |] eqn:?; inv H0.
  destruct (f b2) as [[b2x delta2x] |] eqn:?; try discriminate.
  destruct (f' b2x) as [[b2y delta2y] |] eqn:?; inv H1.
  exploit mi_no_overlap0; eauto. intros A.
  destruct (eq_block b1x b2x).
  subst b1x. destruct A. congruence.
  assert (delta1y = delta2y) by congruence. right; lia.
  exploit mi_no_overlap1. eauto. eauto. eauto.
    eapply perm_inj. eauto. eexact H2. eauto.
    eapply perm_inj. eauto. eexact H3. eauto.
  intuition lia.
(* representable *)
  intros.
  destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate.
  destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H.
  exploit mi_representable0; eauto. intros [A B].
  set (ofs' := Ptrofs.repr (Ptrofs.unsigned ofs + delta1)).
  assert (Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs + delta1).
    unfold ofs'; apply Ptrofs.unsigned_repr. auto.
  exploit mi_representable1. eauto. instantiate (1 := ofs').
  rewrite H.
  replace (Ptrofs.unsigned ofs + delta1 - 1) with
    ((Ptrofs.unsigned ofs - 1) + delta1) by lia.
  destruct H0; eauto using perm_inj.
  rewrite H. lia.
(* perm inv *)
  intros.
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; try discriminate.
  inversion H; clear H; subst b'' delta.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') in H0 by lia.
  exploit mi_perm_inv1; eauto. intros [A|A].
  eapply mi_perm_inv0; eauto.
  right; red; intros. elim A. eapply perm_inj; eauto.
(* src concrete *)
  intros. des_ifs. exploit mi_src_concrete_public1; eauto. i.
  rewrite H. f_equal. lia.
(* src private *)
  i. des_ifs.
  exploit mi_src_concrete_private1; eauto. i.
  destruct ((mem_concrete m1)!b) eqn:H2; clarify.
  exploit mi_src_concrete_public0; eauto. i. clarify.
  exploit mi_src_concrete_private0; eauto.
Qed.

Lemma val_lessdef_inject_compose:
  forall f v1 v2 v3,
  Val.lessdef v1 v2 -> Val.inject f v2 v3 -> Val.inject f v1 v3.
Proof.
  intros. inv H. auto. auto.
Qed.

Lemma val_inject_lessdef_compose:
  forall f v1 v2 v3,
  Val.inject f v1 v2 -> Val.lessdef v2 v3 -> Val.inject f v1 v3.
Proof.
  intros. inv H0. auto. inv H. auto.
Qed.

Lemma extends_inject_compose:
  forall f m1 m2 m3,
  extends m1 m2 -> inject f m2 m3 -> inject f m1 m3.
Proof.
  intros. inversion H; inv H0. constructor; intros.
(* inj *)
  replace f with (compose_meminj inject_id f). eapply mem_inj_compose; eauto.
  apply extensionality; intros. unfold compose_meminj, inject_id.
  destruct (f x) as [[y delta] | ]; auto.
(* unmapped *)
  eapply mi_freeblocks0. erewrite <- valid_block_extends; eauto.
(* mapped *)
  eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_extends; eauto.
(* representable *)
  eapply mi_representable0; eauto.
  destruct H1; eauto using perm_extends.
(* perm inv *)
  exploit mi_perm_inv0; eauto. intros [A|A].
  eapply mext_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_extends; eauto.
(* src concrete*)
  apply mi_src_concrete_public0 with (b1:=b1). assumption.
  eapply mext_concrete with (m2:=m2) (m1:=m1); eauto.
  eapply NNPP. ii. eapply nextblocks_logical in H0; clarify.
(* src private *)
  intros. apply mi_src_concrete_private0 in NOINJECT.
  destruct ((mem_concrete m1) ! b) eqn:M1CONC; eauto.
  eapply mext_concrete0 in M1CONC; eauto; clarify.
  eapply NNPP. ii. eapply nextblocks_logical in H0; clarify.
Qed.

Lemma inject_extends_compose:
  forall f m1 m2 m3,
  inject f m1 m2 -> extends m2 m3 -> inject f m1 m3.
Proof.
  intros. inv H; inversion H0. constructor; intros.
(* inj *)
  replace f with (compose_meminj f inject_id). eapply mem_inj_compose; eauto.
  apply extensionality; intros. unfold compose_meminj, inject_id.
  destruct (f x) as [[y delta] | ]; auto. decEq. decEq. lia.
(* unmapped *)
  eauto.
(* mapped *)
  erewrite <- valid_block_extends; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto.
(* representable *)
  eapply mi_representable0; eauto.
(* perm inv *)
  exploit mext_perm_inv0; eauto. intros [A|A].
  eapply mi_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_inj; eauto.
(* src concrete *)
  eapply mext_concrete with (m1:=m2) (m2:=m3); eauto.
(* src private *)
  eauto.
Qed.

Lemma extends_extends_compose:
  forall m1 m2 m3,
  extends m1 m2 -> extends m2 m3 -> extends m1 m3.
Proof.
  intros. inversion H; subst; inv H0; constructor; intros.
  (* nextblock *)
  congruence.
  (* meminj *)
  replace inject_id with (compose_meminj inject_id inject_id).
  eapply mem_inj_compose; eauto.
  apply extensionality; intros. unfold compose_meminj, inject_id. auto.
  (* perm inv *)
  exploit mext_perm_inv1; eauto. intros [A|A].
  eapply mext_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_extends; eauto.
  (* src private *)
  exploit mext_concrete0; eauto. i.
  exploit mext_concrete1; eauto.
  eapply NNPP. ii. eapply nextblocks_logical in H3; clarify.
Qed.

(** Injecting a memory into itself. *)

Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if plt b thr then Some(b, 0) else None.

Definition inject_neutral (thr: block) (m: mem) :=
  mem_inj (flat_inj thr) m m.

Remark flat_inj_no_overlap:
  forall thr m, meminj_no_overlap (flat_inj thr) m.
Proof.
  unfold flat_inj; intros; red; intros.
  destruct (plt b1 thr); inversion H0; subst.
  destruct (plt b2 thr); inversion H1; subst.
  auto.
Qed.

Theorem neutral_inject:
  forall m, inject_neutral (nextblock m) m -> inject (flat_inj (nextblock m)) m m.
Proof.
  intros. constructor.
(* meminj *)
  auto.
(* freeblocks *)
  unfold flat_inj, valid_block; intros.
  apply pred_dec_false. auto.
(* mappedblocks *)
  unfold flat_inj, valid_block; intros.
  destruct (plt b (nextblock m)); inversion H0; subst. auto.
(* no overlap *)
  apply flat_inj_no_overlap.
(* range *)
  unfold flat_inj; intros.
  destruct (plt b (nextblock m)); inv H0. generalize (Ptrofs.unsigned_range_2 ofs); lia.
(* perm inv *)
  unfold flat_inj; intros.
  destruct (plt b1 (nextblock m)); inv H0.
  rewrite Z.add_0_r in H1; auto.
(* src concrete *)
  i. unfold flat_inj in INJECT.
  des_ifs. rewrite CONCRETE. f_equal. lia.
(* src private *)
  intros. unfold flat_inj in NOINJECT.
  destruct (plt b (nextblock m)) eqn:PLT; inversion NOINJECT.
  apply m.(nextblocks_logical). assumption.
Qed.

Theorem empty_inject_neutral:
  forall thr, inject_neutral thr empty.
Proof.
  intros; red; constructor.
(* perm *)
  unfold flat_inj; intros. destruct (plt b1 thr); inv H.
  replace (ofs + 0) with ofs by lia; auto.
(* align *)
  unfold flat_inj; intros. destruct (plt b1 thr); inv H. apply Z.divide_0_r.
(* mem_contents *)
  intros; simpl. rewrite ! PMap.gi. rewrite ! ZMap.gi. constructor.  
Qed.

Theorem alloc_inject_neutral:
  forall thr m lo hi b m',
  alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  Plt (nextblock m) thr ->
  inject_neutral thr m'.
Proof.
  intros; red.
  eapply alloc_left_mapped_inj with (m1 := m) (b2 := b) (delta := 0).
  eapply alloc_right_inj; eauto. eauto. eauto with mem.
  red. intros. apply Z.divide_0_r.
  intros.
  apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. lia.
  unfold flat_inj.
  apply pred_dec_true.
  rewrite (alloc_result _ _ _ _ _ H). auto.
Qed.

Theorem store_inject_neutral:
  forall chunk m b ofs v m' thr,
  store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  Val.inject (flat_inj thr) v v ->
  inject_neutral thr m'.
Proof.
  intros; red.
  exploit store_mapped_inj. eauto. eauto. apply flat_inj_no_overlap.
  unfold flat_inj.
  apply pred_dec_true; auto. eauto.
  replace (ofs + 0) with ofs by lia.
  intros [m'' [A B]]. congruence.
Qed.

Theorem drop_inject_neutral:
  forall m b lo hi p m' thr,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m'.
Proof.
  unfold inject_neutral; intros.
  exploit drop_mapped_inj; eauto. apply flat_inj_no_overlap.
  unfold flat_inj. apply pred_dec_true; eauto.
  repeat rewrite Z.add_0_r. intros [m'' [A B]]. congruence.
Qed.

(** * Invariance properties between two memory states *)

Section UNCHANGED_ON.

Variable P: block -> Z -> Prop.

Record unchanged_on (m_before m_after: mem) : Prop := mk_unchanged_on {
  unchanged_on_nextblock:
    Ple (nextblock m_before) (nextblock m_after);
  unchanged_on_perm:
    forall b ofs k p,
    P b ofs -> valid_block m_before b ->
    (perm m_before b ofs k p <-> perm m_after b ofs k p);
  unchanged_on_contents:
    forall b ofs,
    P b ofs -> perm m_before b ofs Cur Readable ->
    ZMap.get ofs (PMap.get b m_after.(mem_contents)) =
    ZMap.get ofs (PMap.get b m_before.(mem_contents));
  unchanged_concrete:
    forall b addr,
      valid_block m_before b ->
      m_before.(mem_concrete)!b = Some addr ->
      m_after.(mem_concrete)!b = Some addr;
}.

Lemma unchanged_on_refl:
  forall m, unchanged_on m m.
Proof.
  intros; constructor. apply Ple_refl. tauto. tauto.
  tauto.
Qed.

Lemma valid_block_unchanged_on:
  forall m m' b,
  unchanged_on m m' -> valid_block m b -> valid_block m' b.
Proof.
  unfold valid_block; intros. apply unchanged_on_nextblock in H. extlia.
Qed.

Lemma perm_unchanged_on:
  forall m m' b ofs k p,
  unchanged_on m m' -> P b ofs ->
  perm m b ofs k p -> perm m' b ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto. eapply perm_valid_block; eauto.
Qed.

Lemma perm_unchanged_on_2:
  forall m m' b ofs k p,
  unchanged_on m m' -> P b ofs -> valid_block m b ->
  perm m' b ofs k p -> perm m b ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto.
Qed.

Lemma unchanged_on_trans:
  forall m1 m2 m3, unchanged_on m1 m2 -> unchanged_on m2 m3 -> unchanged_on m1 m3.
Proof.
  intros; constructor.
- apply Ple_trans with (nextblock m2); apply unchanged_on_nextblock; auto.
- intros. transitivity (perm m2 b ofs k p); apply unchanged_on_perm; auto.
  eapply valid_block_unchanged_on; eauto.
- intros. transitivity (ZMap.get ofs (mem_contents m2)#b); apply unchanged_on_contents; auto.
  eapply perm_unchanged_on; eauto.
- intros.
  apply unchanged_concrete with (m_before:=m2); auto.
  unfold valid_block in *.
  assert (H3: Ple (nextblock m1) (nextblock m2)) by (apply unchanged_on_nextblock; assumption).
  apply Plt_Ple_trans with (q:=nextblock m1); assumption.
  apply unchanged_concrete with (m_before:=m1); auto.    
Qed.

Lemma loadbytes_unchanged_on_1:
  forall m m' b ofs n,
  unchanged_on m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m' b ofs n = loadbytes m b ofs n.
Proof.
  intros.
  destruct (zle n 0).
+ erewrite ! loadbytes_empty by assumption. auto.
+ unfold loadbytes. destruct H.
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true. f_equal.
  apply getN_exten. intros. rewrite Z2Nat.id in H by lia.
  apply unchanged_on_contents0; auto.
  red; intros. apply unchanged_on_perm0; auto.
  rewrite pred_dec_false. auto.
  red; intros; elim n0; red; intros. apply <- unchanged_on_perm0; auto.
Qed.

Lemma loadbytes_unchanged_on:
  forall m m' b ofs n bytes,
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m b ofs n = Some bytes ->
  loadbytes m' b ofs n = Some bytes.
Proof.
  intros.
  destruct (zle n 0).
+ erewrite loadbytes_empty in * by assumption. auto.
+ rewrite <- H1. apply loadbytes_unchanged_on_1; auto.
  exploit loadbytes_range_perm; eauto. instantiate (1 := ofs). lia.
  intros. eauto with mem.
Qed.

Lemma not_pure_unchanged_on
    m m' b ofs sz bytes bytes'
    (UNCHANGE: unchanged_on m m')
    (PRED: forall i, ofs <= i < ofs + sz -> P b i)
    (LB1: loadbytes m b ofs sz = Some bytes)
    (LB2: loadbytes m' b ofs sz = Some bytes'):
  <<NPURE: bytes = bytes'>>.
Proof. exploit loadbytes_unchanged_on; eauto. i. clarify. Qed.

Lemma load_unchanged_on_1:
  forall m m' chunk b ofs
  (PURE: forall bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes -> is_mixed_mvs bytes = false),
  unchanged_on m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m' b ofs = load chunk m b ofs.
Proof.
  intros. unfold load. destruct (valid_access_dec m chunk b ofs Readable).
  specialize (PURE (getN (size_chunk_nat chunk) ofs (mem_contents m) # b)).
  exploit PURE.
  { unfold loadbytes. des_ifs. exfalso. eapply n. unfold valid_access in v. des. eauto. }
  assert (LB1: loadbytes m b ofs (size_chunk chunk) =
                 Some (getN (size_chunk_nat chunk) ofs (mem_contents m) # b)).
  { inv v. unfold loadbytes. des_ifs. }
  assert (LB2: loadbytes m' b ofs (size_chunk chunk) =
                 Some (getN (size_chunk_nat chunk) ofs (mem_contents m') # b)).
  { unfold loadbytes. des_ifs_safe. inv v. exfalso. eapply n. ii. exploit H2; eauto. ii.
    eapply perm_unchanged_on; eauto. }
  i. exploit not_pure_unchanged_on; try eapply H2; eauto. i.
  rewrite H3 in H2. erewrite normalize_mvs_pure; eauto. erewrite normalize_mvs_pure; eauto.
  destruct v. rewrite pred_dec_true. f_equal. f_equal. apply getN_exten. intros.
  rewrite <- size_chunk_conv in H6. eapply unchanged_on_contents; eauto.
  split; auto. red; intros. eapply perm_unchanged_on; eauto.
  rewrite pred_dec_false. auto.
  red; intros [A B]; elim n; split; auto. red; intros; eapply perm_unchanged_on_2; eauto.
Qed.

Lemma load_unchanged_on_check_1:
  forall m m' chunk b ofs
  (PURE: forall bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes -> normalize_check chunk bytes = false),
  unchanged_on m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m' b ofs = load chunk m b ofs.
Proof.
  intros. unfold load. destruct (valid_access_dec m chunk b ofs Readable).
- specialize (PURE (getN (size_chunk_nat chunk) ofs (mem_contents m) # b)).
  exploit PURE.
  { unfold loadbytes. des_ifs. exfalso. eapply n. unfold valid_access in v. des. eauto. }
  assert (LB1: loadbytes m b ofs (size_chunk chunk) =
                 Some (getN (size_chunk_nat chunk) ofs (mem_contents m) # b)).
  { inv v. unfold loadbytes. des_ifs. }
  assert (LB2: loadbytes m' b ofs (size_chunk chunk) =
                 Some (getN (size_chunk_nat chunk) ofs (mem_contents m') # b)).
  { unfold loadbytes. des_ifs_safe. inv v. exfalso. eapply n. ii. exploit H2; eauto. ii.
    eapply perm_unchanged_on; eauto. }
  i. exploit not_pure_unchanged_on; try eapply H2; eauto. i.
  unfold normalize_mvs. rewrite H2. rewrite H3 in H2.
  assert (X: normalize_check chunk (getN (size_chunk_nat chunk) ofs (mem_contents m') # b) = false).
  { clear -H2. unfold normalize_check in *. des_ifs. }
  rewrite X. destruct v. rewrite pred_dec_true. f_equal. f_equal. apply getN_exten. intros.
  rewrite <- size_chunk_conv in H6. eapply unchanged_on_contents; eauto.
  split; auto. red; intros. eapply perm_unchanged_on; eauto.
- rewrite pred_dec_false. auto.
  red; intros [A B]; elim n; split; auto. red; intros; eapply perm_unchanged_on_2; eauto.
Qed.

Lemma load_unchanged_on_check_2:
  forall m m' chunk b ofs
  (PURE: forall bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes -> change_check chunk bytes = false),
  unchanged_on m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m' b ofs = load chunk m b ofs.
Proof.
  intros. unfold load. destruct (valid_access_dec m chunk b ofs Readable).
- specialize (PURE (getN (size_chunk_nat chunk) ofs (mem_contents m) # b)).
  exploit PURE.
  { unfold loadbytes. des_ifs. exfalso. eapply n. unfold valid_access in v. des. eauto. }
  assert (LB1: loadbytes m b ofs (size_chunk chunk) =
                 Some (getN (size_chunk_nat chunk) ofs (mem_contents m) # b)).
  { inv v. unfold loadbytes. des_ifs. }
  assert (LB2: loadbytes m' b ofs (size_chunk chunk) =
                 Some (getN (size_chunk_nat chunk) ofs (mem_contents m') # b)).
  { unfold loadbytes. des_ifs_safe. inv v. exfalso. eapply n. ii. exploit H2; eauto. ii.
    eapply perm_unchanged_on; eauto. }
  i. exploit not_pure_unchanged_on; try eapply H2; eauto. i.
  destruct v. rewrite pred_dec_true; cycle 1.
  { split; auto. red; intros. eapply perm_unchanged_on; eauto. }
  f_equal. f_equal. rewrite H3.
  eapply change_check_fail_normalize_mvs_same. erewrite <- H3. eauto.
- rewrite pred_dec_false. auto.
  red; intros [A B]; elim n; split; auto. red; intros; eapply perm_unchanged_on_2; eauto.
Qed.

(* Lemma load_unchanged_on_encoded: *)
(*   forall m m' chunk b ofs *)
(*   (PURE: forall bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes -> encoded_bytes bytes = true), *)
(*   unchanged_on m m' -> *)
(*   valid_block m b -> *)
(*   (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) -> *)
(*   load chunk m' b ofs = load chunk m b ofs. *)
(* Proof. *)
(*   intros. unfold load. destruct (valid_access_dec m chunk b ofs Readable). *)
(*   specialize (PURE (getN (size_chunk_nat chunk) ofs (mem_contents m) # b)). *)
(*   exploit PURE. *)
(*   { unfold loadbytes. des_ifs. exfalso. eapply n. unfold valid_access in v. des. eauto. } *)
(*   assert (LB1: loadbytes m b ofs (size_chunk chunk) = *)
(*                  Some (getN (size_chunk_nat chunk) ofs (mem_contents m) # b)). *)
(*   { inv v. unfold loadbytes. des_ifs. } *)
(*   assert (LB2: loadbytes m' b ofs (size_chunk chunk) = *)
(*                  Some (getN (size_chunk_nat chunk) ofs (mem_contents m') # b)). *)
(*   { unfold loadbytes. des_ifs_safe. inv v. exfalso. eapply n. ii. exploit H2; eauto. ii. *)
(*     eapply perm_unchanged_on; eauto. } *)
(*   i. exploit not_pure_unchanged_on; try eapply H2; eauto. i. *)
(*   rewrite H3 in H2. erewrite decode_normalize_encoded_bytes; eauto. erewrite decode_normalize_encoded_bytes; eauto. *)
(*   destruct v. rewrite pred_dec_true. f_equal. f_equal. f_equal. apply getN_exten. intros. *)
(*   rewrite <- size_chunk_conv in H6. eapply unchanged_on_contents; eauto. *)
(*   split; auto. red; intros. eapply perm_unchanged_on; eauto. *)
(*   rewrite pred_dec_false. auto. *)
(*   red; intros [A B]; elim n; split; auto. red; intros; eapply perm_unchanged_on_2; eauto. *)
(* Qed. *)

Lemma load_unchanged_on_2
  m m' chunk b ofs
  (CONC: m.(mem_concrete) = m'.(mem_concrete))
  (UNCHANGE: unchanged_on m m')
  (VLD: valid_block m b)
  (PRED: forall i, ofs <= i < ofs + size_chunk chunk -> P b i):
  <<SAME: load chunk m' b ofs = load chunk m b ofs>>.
Proof.
  i. unfold load. destruct (valid_access_dec m chunk b ofs Readable).
- erewrite <- normalize_mvs_same_concrete; eauto.
  destruct v. rewrite pred_dec_true.
  2:{ split; auto. red; intros. eapply perm_unchanged_on; eauto. }
  f_equal. f_equal. replace (getN (size_chunk_nat chunk) ofs (mem_contents m') # b)
    with (getN (size_chunk_nat chunk) ofs (mem_contents m) # b); auto.
  apply getN_exten. intros. symmetry. rewrite <- size_chunk_conv in H1. eapply unchanged_on_contents; eauto.
- rewrite pred_dec_false. auto.
  red; intros [A B]; elim n; split; auto. red; intros; eapply perm_unchanged_on_2; eauto.
Qed.

Lemma load_unchanged_on:
  forall m m' chunk b ofs v
  (PURE: forall bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes -> is_mixed_mvs bytes = false),
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m b ofs = Some v ->
  load chunk m' b ofs = Some v.
Proof.
  intros. rewrite <- H1. eapply load_unchanged_on_1; eauto with mem.
Qed.

Lemma load_unchanged_on_check:
  forall m m' chunk b ofs v
  (PURE: forall bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes -> normalize_check chunk bytes = false),
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m b ofs = Some v ->
  load chunk m' b ofs = Some v.
Proof.
  intros. rewrite <- H1. eapply load_unchanged_on_check_1; eauto with mem.
Qed.

Lemma load_unchanged_on_change_check:
  forall m m' chunk b ofs v
  (PURE: forall bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes -> change_check chunk bytes = false),
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m b ofs = Some v ->
  load chunk m' b ofs = Some v.
Proof.
  intros. rewrite <- H1. eapply load_unchanged_on_check_2; eauto with mem.
Qed.

Lemma inject_id_memval_inject_list bytes :
  list_forall2 (memval_inject inject_id) bytes bytes.
Proof.
  ginduction bytes; ss; ii. econs. econs; eauto. destruct a; ss; econs.
  destruct v; ss. unfold inject_id. econs; eauto. rewrite Ptrofs.add_zero. auto.
Qed.

Lemma load_unchanged_on_impure
  m m' chunk b ofs v
  (UNCHANGE: unchanged_on m m')
  (PP: forall i, ofs <= i < ofs + size_chunk chunk -> P b i)
  (LOAD: load chunk m b ofs = Some v):
  exists v', <<LOAD: load chunk m' b ofs = Some v'>> /\ <<REL: v = Vundef \/ v = v'>>.
Proof.
  exploit load_loadbytes; eauto. i. des.
  destruct (normalize_check chunk bytes) eqn:NPURE; cycle 1.
  { exploit (load_unchanged_on_check m m' chunk b ofs v); eauto. ii. clarify. }
  exploit loadbytes_unchanged_on; eauto. intros LB2. rename H into LB1.
  destruct (classic (chunk = Mptr \/ chunk = Many64)); cycle 1.
  { eapply not_or_and in H. des. exploit load_valid_access; eauto. i. inv H2.
    exploit loadbytes_load; try eapply LB2; eauto. i. esplits; eauto.
    right. unfold normalize_mvs, normalize_check. des_ifs_safe. destruct chunk; ss. }
  exploit ( normalize_mvs_decode_val_inject inject_id m m' bytes bytes chunk).
  { erewrite loadbytes_length; eauto. destruct chunk; ss; lia. }
  { ii. inv UNCHANGE. unfold inject_id in H1. clarify. exploit unchanged_concrete0; eauto. i.
    rewrite H0. f_equal. lia. }
  { eapply inject_id_memval_inject_list. }
  i. rewrite <- H0 in H1. exploit loadbytes_load; eauto.
  { exploit load_valid_access; eauto. i. inv H2. auto. }
  i. esplits; eauto. inv H1; auto. unfold inject_id in H4. clarify.
  right. rewrite Ptrofs.add_zero. auto.
Qed.

Lemma load_unchanged_on_concrete
  m m' chunk b ofs v
  (CONC: m.(mem_concrete) = m'.(mem_concrete))
  (UNCHANGE: unchanged_on m m')
  (PRED: forall i, ofs <= i < ofs + size_chunk chunk -> P b i)
  (LOAD: load chunk m b ofs = Some v) :
  <<LOAD: load chunk m' b ofs = Some v>>.
Proof. i. rewrite <- LOAD. eapply load_unchanged_on_2; eauto with mem. Qed.

Lemma store_unchanged_on:
  forall chunk m b ofs v m',
  store chunk m b ofs v = Some m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_store _ _ _ _ _ _ H). apply Ple_refl.
- split; intros; eauto with mem.
- erewrite store_mem_contents; eauto. rewrite PMap.gsspec.
  destruct (peq b0 b); auto. subst b0. apply setN_outside.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (zlt ofs0 ofs); auto.
  destruct (zlt ofs0 (ofs + size_chunk chunk)); auto.
  elim (H0 ofs0). lia. auto.
- rewrite <- H2. rewrite concrete_store with (chunk:=chunk) (b:=b) (ofs:=ofs) (v:=v) (m1:=m) (m2:=m'). reflexivity. assumption.  
Qed.

Lemma storebytes_unchanged_on:
  forall m b ofs bytes m',
  storebytes m b ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z.of_nat (length bytes) -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_storebytes _ _ _ _ _ H). apply Ple_refl.
- split; intros. eapply perm_storebytes_1; eauto. eapply perm_storebytes_2; eauto.
- erewrite storebytes_mem_contents; eauto. rewrite PMap.gsspec.
  destruct (peq b0 b); auto. subst b0. apply setN_outside.
  destruct (zlt ofs0 ofs); auto.
  destruct (zlt ofs0 (ofs + Z.of_nat (length bytes))); auto.
  elim (H0 ofs0). lia. auto.
- rewrite <- H2. rewrite concrete_storebytes with m b ofs bytes m'. reflexivity. assumption.  
Qed.

Lemma alloc_unchanged_on:
  forall m lo hi m' b,
  alloc m lo hi = (m', b) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_alloc _ _ _ _ _ H). apply Ple_succ.
- split; intros.
  eapply perm_alloc_1; eauto.
  eapply perm_alloc_4; eauto.
  eapply valid_not_valid_diff; eauto with mem.
- injection H; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso; auto. rewrite A.  eapply valid_not_valid_diff; eauto with mem.
- rewrite <- H1. rewrite concrete_alloc with (lo:=lo) (hi:=hi) (m2:=m') (b:=b)(m1:=m). reflexivity.
  assumption.
Qed.

Lemma free_unchanged_on:
  forall m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_free _ _ _ _ _ H). apply Ple_refl.
- split; intros.
  eapply perm_free_1; eauto.
  destruct (eq_block b0 b); auto. destruct (zlt ofs lo); auto. destruct (zle hi ofs); auto.
  subst b0. elim (H0 ofs). lia. auto.
  eapply perm_free_3; eauto.
- unfold free in H. destruct (range_perm_dec m b lo hi Cur Freeable); inv H.
  simpl. auto.
- rewrite <- H2. rewrite concrete_free with (bf:=b) (lo:=lo) (hi:=hi) (m2:=m')(m1:=m).
  reflexivity. assumption.
Qed.

Lemma drop_perm_unchanged_on:
  forall m b lo hi p m',
  drop_perm m b lo hi p = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_drop _ _ _ _ _ _ H). apply Ple_refl.
- split; intros. eapply perm_drop_3; eauto.
  destruct (eq_block b0 b); auto.
  subst b0.
  assert (~ (lo <= ofs < hi)). { red; intros; eelim H0; eauto. }
  right; lia.
  eapply perm_drop_4; eauto.
- unfold drop_perm in H.
  destruct (range_perm_dec m b lo hi Cur Freeable); inv H; simpl. auto.
- rewrite <- H2. rewrite concrete_drop with (b:=b) (lo:=lo) (hi:=hi) (p:=p) (m':=m') (m:=m).
  reflexivity. assumption.
Qed.

Lemma capture_unchanged_on:
  forall m b addr m',
  capture m b addr m' -> unchanged_on m m'.
Proof.
  i. inv H. econs; i.
  - rewrite NEXTBLOCK. eapply Ple_refl.
  - unfold perm, perm_order'. rewrite ACCESS. eauto.
  - rewrite CONTENTS. eauto.
  - destruct ((mem_concrete m) ! b) eqn:CONC.
    { exploit PREVADDR; eauto. i. des; subst. rewrite <- H2. eauto. }
    erewrite CAPTURED; eauto.
    destruct (peq b b0); subst; clarify.
    rewrite PTree.gso; eauto.
Qed.

End UNCHANGED_ON.

Lemma unchanged_on_implies:
  forall (P Q: block -> Z -> Prop) m m',
  unchanged_on P m m' ->
  (forall b ofs, Q b ofs -> valid_block m b -> P b ofs) ->
  unchanged_on Q m m'.
Proof.
  intros. destruct H. constructor; intros.
- auto.
- apply unchanged_on_perm0; auto.
- apply unchanged_on_contents0; auto.
  apply H0; auto. eapply perm_valid_block; eauto.
- apply unchanged_concrete0 with (addr:=addr);
    try apply H0; assumption.
Qed.

End Mem.

Notation mem := Mem.mem.

Global Opaque Mem.alloc Mem.free Mem.store Mem.load Mem.storebytes Mem.loadbytes.

Global Hint Resolve
  Mem.valid_not_valid_diff
  Mem.perm_implies
  Mem.perm_cur
  Mem.perm_max
  Mem.perm_valid_block
  Mem.range_perm_implies
  Mem.range_perm_cur
  Mem.range_perm_max
  Mem.valid_access_implies
  Mem.valid_access_valid_block
  Mem.valid_access_perm
  Mem.valid_access_load
  Mem.load_valid_access
  Mem.loadbytes_range_perm
  Mem.valid_access_store
  Mem.perm_store_1
  Mem.perm_store_2
  Mem.nextblock_store
  Mem.store_valid_block_1
  Mem.store_valid_block_2
  Mem.store_valid_access_1
  Mem.store_valid_access_2
  Mem.store_valid_access_3
  Mem.storebytes_range_perm
  Mem.perm_storebytes_1
  Mem.perm_storebytes_2
  Mem.storebytes_valid_access_1
  Mem.storebytes_valid_access_2
  Mem.nextblock_storebytes
  Mem.storebytes_valid_block_1
  Mem.storebytes_valid_block_2
  Mem.nextblock_alloc
  Mem.alloc_result
  Mem.valid_block_alloc
  Mem.fresh_block_alloc
  Mem.valid_new_block
  Mem.perm_alloc_1
  Mem.perm_alloc_2
  Mem.perm_alloc_3
  Mem.perm_alloc_4
  Mem.perm_alloc_inv
  Mem.valid_access_alloc_other
  Mem.valid_access_alloc_same
  Mem.valid_access_alloc_inv
  Mem.range_perm_free
  Mem.free_range_perm
  Mem.nextblock_free
  Mem.valid_block_free_1
  Mem.valid_block_free_2
  Mem.perm_free_1
  Mem.perm_free_2
  Mem.perm_free_3
  Mem.valid_access_free_1
  Mem.valid_access_free_2
  Mem.valid_access_free_inv_1
  Mem.valid_access_free_inv_2
  Mem.unchanged_on_refl
  : mem.
