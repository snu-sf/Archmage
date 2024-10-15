Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Maps.
Require Import Values Memory.
Require Import sflib Classical.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Section BINDEDVAL.

(* m is a target memory *)    

(* merge long and int case *)
Inductive val_intptr (m: mem) : val -> val -> Prop :=
| val_intptr_int : forall i, val_intptr m (Vint i) (Vint i)
| val_intptr_long : forall i, val_intptr m (Vlong i) (Vlong i)
| val_intptr_float : forall f, val_intptr m (Vfloat f) (Vfloat f)
| val_intptr_single : forall f, val_intptr m (Vsingle f) (Vsingle f)
| val_intptr_ptr_ptr : forall b ofs, val_intptr m (Vptr b ofs) (Vptr b ofs)
| val_intptr_ptr_int : forall i b ofs, Archi.ptr64 = false ->
                              Mem.to_int (Vptr b ofs) m = Some (Vint i) ->
                              val_intptr m (Vptr b ofs) (Vint i)
| val_intptr_ptr_long : forall i b ofs, Archi.ptr64 = true ->
                               Mem.to_int (Vptr b ofs) m = Some (Vlong i) ->
                               val_intptr m (Vptr b ofs) (Vlong i)
| val_intptr_undef : forall v, val_intptr m Vundef v.

Inductive val_intptrist (m: mem) : list val -> list val -> Prop :=
| val_intptr_nil : val_intptrist m [] []
| val_intptr_cons : forall v1 v2 vl1 vl2, val_intptr m v1 v2 ->
                                 val_intptrist m vl1 vl2 ->
                                 val_intptrist m (v1::vl1) (v2::vl2).

Lemma val_intptr_refl m v :
  val_intptr m v v.
Proof. destruct v; ss; econs. Qed.

End BINDEDVAL.

Section BINDMVAL.

(** * Compatibility with concrete extends *)

(** Relating two memory values according to a concrete extends. *)

(* TODO: merge 2nd 3rd case *)
Inductive memval_intptr (m: mem) : memval -> memval -> Prop :=
| memval_intptr_byte:
  forall n, memval_intptr m (Byte n) (Byte n)
| memval_intptr_byte_frag64:
  forall b ofs i bl bt n,
    Archi.ptr64 = true ->
    Mem.to_int (Vptr b ofs) m = Some (Vlong i) ->
    encode_val Mptr (Vlong i) = bl ->
    nth_error (rev_if_be_mv bl) n = Some (Byte bt) ->
    memval_intptr m (Fragment (Vptr b ofs) Q64 n) (Byte bt)
| memval_intptr_byte_frag32:
  forall b ofs i bl bt n,
    Archi.ptr64 = false ->
    Mem.to_int (Vptr b ofs) m = Some (Vint i) ->
    encode_val Mptr (Vint i) = bl ->
    nth_error (rev_if_be_mv bl) n = Some (Byte bt) ->
    memval_intptr m (Fragment (Vptr b ofs) Q32 n) (Byte bt)
| memval_intptr_frag:
  forall v1 v2 q n,
    val_intptr m v1 v2 ->
    memval_intptr m (Fragment v1 q n) (Fragment v2 q n)
| memval_intptr_undef_frag:
  forall q n mv, memval_intptr m (Fragment Vundef q n) mv
| memval_intptr_undef:
  forall mv, memval_intptr m Undef mv.

Lemma memval_intptr_refl m mv :
  memval_intptr m mv mv.
Proof. destruct mv; ss; econs. destruct v; econs. Qed.
  
End BINDMVAL.

Section CHANGE_EXT.

Record concrete_extends (m_before m_after: mem) : Prop := mk_concrete_extends {
  same_nextblock:
    (Mem.nextblock m_before) = (Mem.nextblock m_after);
  extended_access:
      forall b ofs k p, Mem.perm m_before b ofs k p ->
                   Mem.perm m_after b ofs k p;                                                         
  extended_contents:
    forall b ofs,
    Mem.perm m_before b ofs Cur Readable ->
    memval_intptr m_after (ZMap.get ofs (Mem.mem_contents m_before) # b) (ZMap.get ofs (Mem.mem_contents m_after) # b);
  extended_concrete:
    forall b caddr,
    m_before.(Mem.mem_concrete) ! b = Some caddr -> m_after.(Mem.mem_concrete) ! b = Some caddr;
}.

Lemma concrete_ext_refl:
  forall m, concrete_extends m m.
Proof. i; econs; eauto. ii. eapply memval_intptr_refl. Qed.

Lemma concrete_concrete_implies m m' b caddr
  (CE: concrete_extends m m')
  (CONC: m.(Mem.mem_concrete) ! b = Some caddr):
  <<CONC: m'.(Mem.mem_concrete) ! b = Some caddr>>.
Proof. inv CE. eauto. Qed.

Lemma valid_concrete_extends m m'
  (CE: concrete_extends m m') b ofs:
  Mem.valid_pointer m b ofs = true -> Mem.valid_pointer m' b ofs = true.
Proof.
  inv CE. unfold Mem.valid_pointer.
  destruct (Mem.perm_dec m b ofs Cur Nonempty); destruct (Mem.perm_dec m' b ofs Cur Nonempty); ss.
  exfalso. eapply n; eauto.
Qed.

Lemma weak_valid_concrete_extends m m'
  (CE: concrete_extends m m') b ofs :
  Mem.weak_valid_pointer m b ofs = true -> Mem.weak_valid_pointer m' b ofs = true.
Proof.
  unfold Mem.weak_valid_pointer. i. eapply orb_prop in H. des.
  - eapply valid_concrete_extends in H; eauto. rewrite H. ss.
  - eapply valid_concrete_extends in H; eauto. rewrite H. eapply orb_true_r.
Qed.

Lemma _valid_concrete_extends m m'
  (CE: concrete_extends m m') b ofs k :
  Mem._valid_pointer m.(Mem.mem_access) b ofs k -> Mem._valid_pointer m'.(Mem.mem_access) b ofs k.
Proof. unfold Mem._valid_pointer. i. eapply extended_access; eauto. Qed.

Lemma _weak_valid_concrete_extends m m'
  (CE: concrete_extends m m') b ofs k:
  Mem._weak_valid_pointer m.(Mem.mem_access) b ofs k -> Mem._weak_valid_pointer m'.(Mem.mem_access) b ofs k.
Proof. unfold Mem._weak_valid_pointer. i. des; eapply _valid_concrete_extends in H; eauto. Qed.

Lemma denormalize_concrete_extends
  m z m' b ofs
  (CE: concrete_extends m m')
  (DENO: Mem.denormalize z m = Some (b, ofs)):
  <<DENOTGT: Mem.denormalize z m' = Some (b, ofs)>>.
Proof.
  inv CE. unfold Mem.denormalize in DENO.
  eapply PTree.gselectf in DENO. des. unfold Mem.denormalize_aux in *.
  rewrite DENO in *. des_ifs_safe.
  eapply andb_prop in Heq. des.
  rewrite <- Mem.addr_in_block_iff in Heq0.
  
  inv Heq0. des. clarify.
  exploit extended_access0.
  { unfold Mem.perm. erewrite PERM. ss. eapply perm_any_N. }
  eapply extended_concrete0 in CONCRETE.
  unfold Mem.is_valid in Heq. rewrite same_nextblock0 in *.

  assert (INBLKTGT: Mem.addr_in_block (Mem.mem_concrete m') (Mem.mem_access m') z b).
  { exploit extended_access0.
    { unfold Mem.perm. erewrite PERM. ss. eapply perm_any_N. }
    i. unfold Mem.perm, Mem.perm_order' in H. des_ifs.
    econs; eauto. }

  destruct (Mem.denormalize z m') eqn:TGT.
  { unfold Mem.denormalize in TGT. eapply PTree.gselectf in TGT.
    des. unfold Mem.denormalize_aux in TGT0. des_ifs.
    eapply andb_prop in Heq1. des.
    rewrite <- Mem.addr_in_block_iff in Heq2.
    exploit Mem.no_concrete_overlap. eapply INBLKTGT. eauto. ii. subst. clarify. }
  eapply PTree.gselectnf in TGT. exfalso. eapply TGT. esplits; eauto. 
  ii. unfold Mem.denormalize_aux in H. des_ifs. rewrite andb_false_iff in Heq1. des.
  { unfold Mem.is_valid in Heq1. clarify. }
  rewrite Mem.addr_in_block_iff in INBLKTGT. clarify.
Qed.

Lemma concrete_extends_perm_implies m m'
    (CE: concrete_extends m m') b o k p :
  Mem.perm m b o k p -> Mem.perm m' b o k p.
Proof. eapply extended_access; eauto. Qed.

Lemma concrete_extends_range_perm_implies m m'
    (CE: concrete_extends m m') b o l k p :
  Mem.range_perm m b o l k p -> Mem.range_perm m' b o l k p.
Proof. unfold Mem.range_perm; i. eapply concrete_extends_perm_implies; eauto. Qed.

(* Lemma denormalize_concrete_extends_same_addr m m' *)
(*     (CE: concrete_extends m m') *)
(*     i1 i2 b o *)
(*     (DENO1: Mem.denormalize i1 m = Some (b, o)) *)
(*     (DENO2: Mem.denormalize i2 m' = Some (b, o)): *)
(*   <<SAMEADD: i1 = i2>>. *)
(* Proof. *)
(*   eapply PTree.gselectf in DENO1, DENO2. *)
(*   des. unfold Mem.denormalize_aux in *. des_ifs. *)
(*   assert (a0 = a). *)
(*   { eapply extended_concrete in Heq1; eauto. clarify. } *)
(*   clarify. eapply Mem.Z_sub_reg_r; eauto. *)
(* Qed. *)

End CHANGE_EXT.

Lemma ptr2int_conc_ext (m m': mem) b ofs addr
   (CONCEXT: concrete_extends m m')
   (P2I: Mem.ptr2int b ofs m = Some addr) :  
  Mem.ptr2int b ofs m' = Some addr.
Proof.
  unfold Mem.ptr2int in *. des_ifs_safe.
  eapply extended_concrete in Heq; eauto.
  rewrite Heq. auto.
Qed.

Lemma to_ptr_concrete_exnteds_tgt
    m m' v1 v1' b ofs k
    (CONCEXT: concrete_extends m m')
    (BIND: val_intptr m' v1 v1')
    (PERM: Mem.perm m' b (Ptrofs.unsigned ofs) k Nonempty) 
    (I2P: Mem.to_ptr v1 m = Some (Vptr b ofs)) :
  Mem.to_ptr v1' m' = Some (Vptr b ofs).
Proof.
  ss. dup BIND. inv BIND; ss; des_ifs_safe.
  - des_ifs.
    { eapply denormalize_concrete_extends in Heq1; eauto. des; clarify. }
    { eapply denormalize_concrete_extends in Heq1; eauto. des; clarify. }
  - exploit Mem.ptr2int_to_denormalize_max; eauto.
    { eapply Ptrofs.unsigned_range_2. }
    { eapply Mem.perm_max; eauto. }
    i. des. exploit Mem.denormalize_info; eauto. i. des.
    unfold Ptrofs.max_unsigned in *. erewrite Ptrofs.modulus_eq64 in *; eauto.
    destruct (Int64.eq (Int64.repr z) Int64.zero) eqn:NULL.
    { exfalso. unfold Int64.eq in NULL. erewrite Int64.unsigned_zero in NULL. des_ifs.
      erewrite Int64.unsigned_repr in e; subst; [lia|].
      unfold Int64.max_unsigned. lia. }
    erewrite Int64.unsigned_repr.
    2:{ unfold Int64.max_unsigned. lia. }
    rewrite H0. rewrite Ptrofs.repr_unsigned. eauto.
Qed.

Lemma to_ptr_concrete_exnteds
    m m' v1 v1' b ofs k
    (CONCEXT: concrete_extends m m')
    (BIND: val_intptr m' v1 v1')
    (PERM: Mem.perm m b (Ptrofs.unsigned ofs) k Nonempty) 
    (I2P: Mem.to_ptr v1 m = Some (Vptr b ofs)) :
  Mem.to_ptr v1' m' = Some (Vptr b ofs).
Proof.
  eapply concrete_extends_perm_implies in PERM; eauto.
  eapply to_ptr_concrete_exnteds_tgt; eauto.
Qed.

(** to_ptr, to_int function & lemmas for wrapper operation *)

Definition option_to_val (ov: option val) : val :=
  match ov with
  | Some v => v
  | None => Vundef
  end.

Definition to_ptr_val (m: mem) (v: val) : val :=
  option_to_val (Mem.to_ptr v m).

Definition to_int_val (m: mem) (v: val) : val :=
  option_to_val (Mem.to_int v m).

Lemma to_ptr_val_ptr_or_undef m v v'
    (TOPTR: to_ptr_val m v = v') :
  v' = Vundef \/ exists b ofs, v' = Vptr b ofs \/ v' = Vnullptr.
Proof.
  unfold to_ptr_val, Mem.to_ptr in TOPTR. destruct v; ss; des_ifs; eauto.
  right. unfold option_to_val. esplits; eauto.
  Unshelve. eapply 1%positive. eapply Ptrofs.zero.
Qed.

Lemma to_int_val_int_or_undef m v v'
    (TOINT: to_int_val m v = v') :
  v' = Vundef \/ exists n, v' = Vlong n \/ exists n, v' = Vint n.
Proof.
  unfold to_int_val, Mem.to_int in TOINT. destruct v; ss; des_ifs; eauto.
  ss. eauto.
  Unshelve. eapply Int64.zero.
Qed.

Lemma nullptr_to_ptr_nullptr m:
  <<FAIL: to_ptr_val m Vnullptr = Vnullptr>>.
Proof.
  unfold to_ptr_val, Mem.to_ptr, Vnullptr. simpl. des_ifs.
Qed.

Lemma nullptr_to_ptr_nullptr32 (SF: Archi.ptr64 = false) m:
  <<FAIL: to_ptr_val m (Vint Int.zero) = Vint Int.zero>>.
Proof.
  specialize (nullptr_to_ptr_nullptr m). i. unfold Vnullptr in *.
  rewrite SF in *. eauto.
Qed.

Lemma ptr_to_int_never_nullptr b ofs m
    (WVLD: Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) = true) :
  <<NOTNULL: to_int_val m (Vptr b ofs) <> Vnullptr>>.
Proof.
  unfold to_int_val, Mem.to_int, Mem.ptr2int_v. simpl. des_ifs.
  eapply Mem.ptr2int_weak_valid' in Heq; eauto; [| eapply Ptrofs.unsigned_range_2].
  i. des. ii. simpl in *. unfold Vnullptr in H. destruct Archi.ptr64 eqn:SF.
  - assert (Int64.eq (Int64.repr z) Int64.zero).
    { inv H; des_ifs. }
    inv INRANGE. simpl in *. unfold Int64.eq in H0. rewrite Int64.unsigned_repr in H0.
    2:{ simpl in *. rewrite Ptrofs.modulus_eq64 in SND; eauto. unfold Int64.max_unsigned. lia. }
    rewrite Int64.unsigned_zero in H0. des_ifs; lia.
  - assert (Int.eq (Int.repr z) Int.zero).
    { inv H; des_ifs. }
    inv INRANGE. simpl in *. unfold Int.eq in H0. rewrite Int.unsigned_repr in H0.
    2:{ simpl in *. rewrite Ptrofs.modulus_eq32 in SND; eauto. unfold Int.max_unsigned. lia. }
    rewrite Int.unsigned_zero in H0. des_ifs; lia.
Qed.

Section GENINJ.

Variable m1 m2: mem.
Variable f: meminj.

Hypothesis mi_inj_perm: forall b1 b2 delta ofs k p,
    f b1 = Some (b2, delta) ->
    Mem.perm m1 b1 ofs k p -> Mem.perm m2 b2 (ofs + delta) k p.

Hypothesis src_concrete_private: forall b, f b = None -> (Mem.mem_concrete m1) ! b = None.

Hypothesis mappedblocks: forall b b' delta, Mem.valid_block m1 b -> f b = Some (b', delta) -> Mem.valid_block m2 b'.

Hypothesis src_concrete_public: forall b1 b2 addr delta,
    f b1 = Some (b2, delta) ->
    (Mem.mem_concrete m1) ! b1 = Some addr ->
    (Mem.mem_concrete m2) ! b2 = Some (addr - delta).

Hypothesis representable: forall b b' delta ofs,
    f b = Some (b', delta) ->
    Mem.perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/
    Mem.perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
    delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned.

Lemma to_ptr_val_inject' v v'
    (VINJ: Val.inject f v v') :
  <<INJ: Val.inject f (to_ptr_val m1 v) (to_ptr_val m2 v')>>.
Proof.
  unfold to_ptr_val. destruct (Mem.to_ptr v m1) eqn:SRC; ss.
  exploit Mem.to_ptr_inject'; eauto. i. des. rewrite TOPTRTGT. ss.
Qed.

Lemma to_int_val_inject' v v'
    (VINJ: Val.inject f v v') :
  <<INJ: Val.inject f (to_int_val m1 v) (to_int_val m2 v')>>.
Proof.
  unfold to_int_val. destruct (Mem.to_int v m1) eqn:SRC; ss.
  exploit Mem.to_int_inject'; eauto. i. des. rewrite TOINTTGT. ss.
Qed.

End GENINJ.

Lemma to_ptr_val_lessdef m m' v v'
    (MEXT: Mem.extends m m')
    (VINJ: Val.lessdef v v') :
  <<LESS': Val.lessdef (option_to_val (Mem.to_ptr v m)) (option_to_val (Mem.to_ptr v' m'))>>.
Proof.
  destruct (Mem.to_ptr v m) eqn:SRC; ss.
  exploit Mem.to_ptr_extends; eauto. i. des. rewrite H. ss.
Qed.
        
Lemma to_ptr_val_list_lessdef m m' vl vl'
    (MEXT: Mem.extends m m')
    (VLESS: Val.lessdef_list vl vl') :
  <<LESS: Val.lessdef_list (map (to_ptr_val m) vl) (map (to_ptr_val m') vl')>>.
Proof.
  induction VLESS; ss. econs; eauto. eapply to_ptr_val_lessdef; eauto.
Qed.

Lemma to_int_val_lessdef m m' v v'
    (MEXT: Mem.extends m m')
    (VINJ: Val.lessdef v v') :
  <<LESS': Val.lessdef (option_to_val (Mem.to_int v m)) (option_to_val (Mem.to_int v' m'))>>.
Proof.
  destruct (Mem.to_int v m) eqn:SRC; ss.
  exploit Mem.to_int_extends; eauto. i. des. rewrite H. ss.
Qed.

Lemma to_int_val_list_lessdef m m' vl vl'
    (MEXT: Mem.extends m m')
    (VLESS: Val.lessdef_list vl vl') :
  <<LESS: Val.lessdef_list (map (to_int_val m) vl) (map (to_int_val m') vl')>>.
Proof.
  induction VLESS; ss. econs; eauto. eapply to_int_val_lessdef; eauto.
Qed.

Lemma to_ptr_val_inject f m m' v v'
    (MINJ: Mem.inject f m m')
    (VINJ: Val.inject f v v') :
  <<INJ: Val.inject f (to_ptr_val m v) (to_ptr_val m' v')>>.
Proof. inv MINJ. eapply to_ptr_val_inject'; eauto. inv mi_inj; eauto. Qed.

Lemma to_ptr_val_list_inject f m m' vl vl'
    (MINJ: Mem.inject f m m')
    (VINJ: Val.inject_list f vl vl') :
  <<INJ: Val.inject_list f (map (to_ptr_val m) vl) (map (to_ptr_val m') vl')>>.
Proof. induction VINJ; ss. econs; eauto. eapply to_ptr_val_inject; eauto. Qed.

Lemma to_int_val_inject f m m' v v'
    (MINJ: Mem.inject f m m')
    (VINJ: Val.inject f v v') :
  <<INJ: Val.inject f (to_int_val m v) (to_int_val m' v')>>.
Proof. inv MINJ. eapply to_int_val_inject'; eauto. Qed.

Lemma to_int_val_list_inject f m m' vl vl'
    (MINJ: Mem.inject f m m')
    (VINJ: Val.inject_list f vl vl') :
  <<INJ: Val.inject_list f (map (to_int_val m) vl) (map (to_int_val m') vl')>>.
Proof. induction VINJ; ss. econs; eauto. eapply to_int_val_inject; eauto. Qed.

(** Auxiliary Lemmas for comparison *)

(* Lemma same_block_concrete_cmp64 *)
(*   caddr caddr' m b ofs ofs' c *)
(*   (BIT: Archi.ptr64 = true) *)
(*   (PTR1: Mem.denormalize (Int64.unsigned caddr) m = Some (b, ofs)) *)
(*   (PTR2: Mem.denormalize (Int64.unsigned caddr') m = Some (b, ofs')) *)
(*   : *)
(*   <<CMP: Ptrofs.cmpu c (Ptrofs.repr ofs) (Ptrofs.repr ofs') = Int64.cmpu c caddr caddr' >>. *)
(* Proof. *)
(*   exploit Mem.denormalize_in_range; try eapply PTR1. *)
(*   exploit Mem.denormalize_in_range; try eapply PTR2. intros ORANGE1 ORANGE2. *)
(*   exploit Mem.denormalize_paddr_in_range; try eapply PTR1. *)
(*   exploit Mem.denormalize_paddr_in_range; try eapply PTR2. intros PRANGE1 PRANGE2. *)
(*   eapply PTree.gselectf in PTR1, PTR2. des. unfold Mem.denormalize_aux in *. des_ifs. *)
(*   eapply andb_prop in Heq0, Heq2. des. r. *)
(*   unfold Mem.addr_is_in_block in *. des_ifs. *)
(*   destruct c. *)
(*   - unfold Ptrofs.cmpu, Ptrofs.eq. *)
(*     rewrite Ptrofs.unsigned_repr; [|unfold Ptrofs.max_unsigned in *; lia]. *)
(*     rewrite Ptrofs.unsigned_repr; [|unfold Ptrofs.max_unsigned in *; lia]. *)
(*     unfold Int64.cmpu, Int64.eq. des_ifs; lia. *)
(*   - unfold Ptrofs.cmpu, Ptrofs.eq. *)
(*     rewrite Ptrofs.unsigned_repr; [|unfold Ptrofs.max_unsigned in *; lia]. *)
(*     rewrite Ptrofs.unsigned_repr; [|unfold Ptrofs.max_unsigned in *; lia]. *)
(*     unfold Int64.cmpu, Int64.eq. des_ifs; lia. *)
(*   - simpl. unfold Ptrofs.ltu, Int64.ltu. *)
(*     rewrite Ptrofs.unsigned_repr; [|unfold Ptrofs.max_unsigned in *; lia]. *)
(*     rewrite Ptrofs.unsigned_repr; [|unfold Ptrofs.max_unsigned in *; lia]. *)
(*     des_ifs; lia. *)
(*   - simpl. unfold Ptrofs.ltu, Int64.ltu. *)
(*     rewrite Ptrofs.unsigned_repr; [|unfold Ptrofs.max_unsigned in *; lia]. *)
(*     rewrite Ptrofs.unsigned_repr; [|unfold Ptrofs.max_unsigned in *; lia]. *)
(*     des_ifs; lia. *)
(*   - simpl. unfold Ptrofs.ltu, Int64.ltu. *)
(*     rewrite Ptrofs.unsigned_repr; [|unfold Ptrofs.max_unsigned in *; lia]. *)
(*     rewrite Ptrofs.unsigned_repr; [|unfold Ptrofs.max_unsigned in *; lia]. *)
(*     des_ifs; lia. *)
(*   - simpl. unfold Ptrofs.ltu, Int64.ltu. *)
(*     rewrite Ptrofs.unsigned_repr; [|unfold Ptrofs.max_unsigned in *; lia]. *)
(*     rewrite Ptrofs.unsigned_repr; [|unfold Ptrofs.max_unsigned in *; lia]. *)
(*     des_ifs; lia. *)
(* Qed. *)

Lemma lt_eq_cmpu ofs1 ofs2 i1 i2 c
    (EQ: Ptrofs.eq ofs1 ofs2 = Int.eq i1 i2)
    (LT: Ptrofs.ltu ofs1 ofs2 = Int.ltu i1 i2) :
  <<CMPU: Ptrofs.cmpu c ofs1 ofs2 = Int.cmpu c i1 i2>>.
Proof.
  destruct c; simpl in *.
  - rewrite EQ. reflexivity.
  - rewrite EQ. reflexivity.
  - rewrite LT. reflexivity.
  - rewrite Ptrofs.not_ltu, Int.not_ltu. rewrite EQ, LT. reflexivity.
  - rewrite Ptrofs.ltu_not, Int.ltu_not. rewrite EQ, LT. reflexivity.
  - rewrite LT. reflexivity.
Qed.

Lemma lt_eq_cmplu ofs1 ofs2 i1 i2 c
    (EQ: Ptrofs.eq ofs1 ofs2 = Int64.eq i1 i2)
    (LT: Ptrofs.ltu ofs1 ofs2 = Int64.ltu i1 i2) :
  <<CMPU: Ptrofs.cmpu c ofs1 ofs2 = Int64.cmpu c i1 i2>>.
Proof.
  destruct c; simpl in *.
  - rewrite EQ. reflexivity.
  - rewrite EQ. reflexivity.
  - rewrite LT. reflexivity.
  - rewrite Ptrofs.not_ltu, Int64.not_ltu. rewrite EQ, LT. reflexivity.
  - rewrite Ptrofs.ltu_not, Int64.ltu_not. rewrite EQ, LT. reflexivity.
  - rewrite LT. reflexivity.
Qed.

(** Auxiliary Lemmas for ptr comparison and pointer sub *)

(** No Angelic Behavior in CompCert *)

Lemma psub_wrapper_no_angelic m v1 v2 vp vi
    (SUB1: Val.psub (to_ptr_val m v1) (to_ptr_val m v2) = vp)
    (SUB2: Val.psub (to_int_val m v1) (to_int_val m v2) = vi) :
  <<NOANGELIC: vp = Vundef \/ vi = Vundef \/ vi = vp>>.
Proof.
  destruct (Archi.ptr64) eqn:BIT.
  { unfold Val.psub in *. rewrite BIT in *. clear BIT.
    destruct v1; destruct v2; simpl in *; subst; eauto.
    all: (des_ifs; eauto). }
  destruct v1; simpl in *; subst; try rewrite BIT; [auto| | auto | auto | auto | ].
  - destruct v2; simpl in *; subst; try rewrite BIT; [auto| | auto | auto | auto | ].
    (* int int *)
    + unfold to_ptr_val. simpl. rewrite BIT. simpl.
      destruct (Int.eq i Int.zero) eqn: NULL.
      { destruct (Int.eq i0 Int.zero) eqn: NULL'.
        - simpl. eapply Int.same_if_eq in NULL, NULL'. subst. eauto.
        - destruct (Mem.denormalize (Int.unsigned i0) m) eqn:DENO2; simpl; eauto. }
      destruct (Int.eq i0 Int.zero) eqn: NULL'.
      { destruct (Mem.denormalize (Int.unsigned i) m) eqn:DENO; simpl; eauto.
        destruct p. simpl. eauto. }
      destruct (Mem.denormalize (Int.unsigned i) m) eqn:DENO1; simpl;[|auto]. destruct p. simpl.
      destruct (Mem.denormalize (Int.unsigned i0) m) eqn:DENO2; simpl; [|auto]. destruct p. simpl.
      rewrite BIT. destruct (eq_block b b0); [|auto]. symmetry in e; subst.
      exploit Mem.denormalize_info; try eapply DENO1. i. des.
      exploit Mem.denormalize_info; try eapply DENO2. i. des. subst.
      rewrite CONC in CONC0. inv CONC0. do 2 right. unfold Ptrofs.sub.
      rewrite Ptrofs.unsigned_repr; [|lia]. rewrite Ptrofs.unsigned_repr; [|lia].
      replace (Int.unsigned i - caddr0 - (Int.unsigned i0 - caddr0)) with (Int.unsigned i - Int.unsigned i0) by lia.
      unfold Int.sub, Ptrofs.to_int. f_equal. eapply Int.same_if_eq. unfold Int.eq.
      do 2 rewrite Int.unsigned_repr_eq. rewrite Ptrofs.unsigned_repr_eq. rewrite Ptrofs.modulus_eq32; eauto.
      rewrite Z.mod_mod; [des_ifs|]. specialize Int.modulus_pos. lia.
    (* int ptr *)
    + unfold to_ptr_val, to_int_val. simpl. rewrite BIT. simpl.
      destruct (Int.eq i Int.zero) eqn: NULL; simpl; eauto.
      destruct (Mem.denormalize (Int.unsigned i) m) eqn:DENO1; simpl; [|auto]. destruct p. simpl.
      rewrite BIT. destruct (eq_block b0 b); [|auto]. subst.
      destruct (Mem.ptr2int b (Ptrofs.unsigned i0) m) eqn:I2P; simpl; [|auto].
      right. right. eapply Mem.denormalize_info in DENO1. des.
      unfold Mem.ptr2int in I2P. rewrite CONC in I2P. subst. inv I2P.
      f_equal. unfold Int.sub, Ptrofs.sub, Ptrofs.to_int.
      do 2 rewrite Ptrofs.unsigned_repr_eq. eapply Int.same_if_eq. unfold Int.eq.
      do 3 rewrite Int.unsigned_repr_eq. rewrite Zminus_mod_idemp_l. rewrite Zminus_mod_idemp_r.
      rewrite Ptrofs.modulus_eq32; eauto.
      replace (Int.unsigned i - (caddr + Ptrofs.unsigned i0)) with (Int.unsigned i - caddr - Ptrofs.unsigned i0) by lia.
      rewrite Z.mod_mod; [des_ifs|]. specialize Int.modulus_pos. lia.
  - destruct v2; simpl in *; subst; try rewrite BIT; [auto| | auto | auto | auto | ].
    (* ptr int *)
    + unfold to_ptr_val, to_int_val. simpl. rewrite BIT. simpl.
      destruct (Int.eq i0 Int.zero) eqn: NULL; simpl; eauto.
      destruct (Mem.denormalize (Int.unsigned i0) m) eqn:DENO2; simpl; [|auto]. destruct p. simpl.
      destruct (eq_block b b0); [|auto]. symmetry in e. subst.
      destruct (Mem.ptr2int b (Ptrofs.unsigned i) m) eqn:I2P; simpl; [|auto]. rewrite BIT.
      right. right. eapply Mem.denormalize_info in DENO2. des.
      unfold Mem.ptr2int in I2P. rewrite CONC in I2P. subst. inv I2P.
      f_equal. unfold Int.sub, Ptrofs.sub, Ptrofs.to_int.
      do 2 rewrite Ptrofs.unsigned_repr_eq. eapply Int.same_if_eq. unfold Int.eq.
      do 3 rewrite Int.unsigned_repr_eq. rewrite Zminus_mod_idemp_l. rewrite Zminus_mod_idemp_r.
      rewrite Ptrofs.modulus_eq32; eauto.
      replace (Ptrofs.unsigned i - (Int.unsigned i0 - caddr)) with (caddr + Ptrofs.unsigned i - Int.unsigned i0) by lia.
      rewrite Z.mod_mod; [des_ifs|]. specialize Int.modulus_pos. lia.
    + unfold to_ptr_val in *. simpl. rewrite BIT. simpl. auto.
    + destruct (eq_block b b0); [|auto]. unfold to_int_val. simpl. subst b0.
      destruct (Mem.ptr2int b (Ptrofs.unsigned i) m) eqn:P2I; simpl; [|auto].
      destruct (Mem.ptr2int b (Ptrofs.unsigned i0) m) eqn:P2I'; simpl; [|auto]. rewrite BIT.
      unfold Mem.ptr2int in *. destruct ((Mem.mem_concrete m)!b); [|clarify].
      inv P2I; inv P2I'. right. right. simpl. rewrite BIT.
      unfold Int.sub, Ptrofs.to_int, Ptrofs.sub. f_equal. eapply Int.same_if_eq. unfold Int.eq.
      repeat rewrite Int.unsigned_repr_eq. rewrite Ptrofs.unsigned_repr_eq. rewrite Ptrofs.modulus_eq32; eauto.
      rewrite Zminus_mod_idemp_l. rewrite Zminus_mod_idemp_r.
      replace (z1 + Ptrofs.unsigned i - (z1 + Ptrofs.unsigned i0)) with (Ptrofs.unsigned i - Ptrofs.unsigned i0) by lia.
      rewrite Z.mod_mod; [des_ifs|]. specialize Int.modulus_pos. lia.
Qed.

Lemma psubl_wrapper_no_angelic m v1 v2 vp vi
    (SUB1: Val.psubl (to_ptr_val m v1) (to_ptr_val m v2) = vp)
    (SUB2: Val.psubl (to_int_val m v1) (to_int_val m v2) = vi) :
  <<NOANGELIC: vp = Vundef \/ vi = Vundef \/ vi = vp>>.
Proof.
  destruct (Archi.ptr64) eqn:BIT; cycle 1.
  { unfold Val.psubl in *. rewrite BIT in *. clear BIT.
    destruct v1; destruct v2; simpl in *; subst; eauto.
    all: (des_ifs; eauto). }
  destruct v1; simpl in *; subst; try rewrite BIT; [auto | auto | | auto | auto | ].
  - destruct v2; simpl in *; subst; try rewrite BIT; [auto | auto | | auto | auto | ].
    (* int int *)
    + unfold to_ptr_val. simpl. rewrite BIT. simpl.
      destruct (Int64.eq i Int64.zero) eqn: NULL.
      { destruct (Int64.eq i0 Int64.zero) eqn: NULL'.
        - simpl. (* rewrite BIT. *) eapply Int64.same_if_eq in NULL, NULL'. subst. eauto.
        - destruct (Mem.denormalize (Int64.unsigned i0) m) eqn:DENO2; simpl; eauto.
          destruct p. simpl. eauto. }
      destruct (Int64.eq i0 Int64.zero) eqn: NULL'.
      { destruct (Mem.denormalize (Int64.unsigned i) m) eqn:DENO; simpl; eauto.
        destruct p. simpl. eauto. }
      destruct (Mem.denormalize (Int64.unsigned i) m) eqn:DENO1; simpl;[|auto]. destruct p. simpl.
      destruct (Mem.denormalize (Int64.unsigned i0) m) eqn:DENO2; simpl; [|auto]. destruct p. simpl.
      rewrite BIT. destruct (eq_block b b0); [|auto]. symmetry in e; subst.
      exploit Mem.denormalize_info; try eapply DENO1. i. des.
      exploit Mem.denormalize_info; try eapply DENO2. i. des. subst. simpl.
      rewrite CONC in CONC0. inv CONC0. do 2 right. unfold Ptrofs.sub.
      rewrite Ptrofs.unsigned_repr; [|lia]. rewrite Ptrofs.unsigned_repr; [|lia].
      replace (Int64.unsigned i - caddr0 - (Int64.unsigned i0 - caddr0)) with (Int64.unsigned i - Int64.unsigned i0) by lia.
      unfold Int64.sub, Ptrofs.to_int64. f_equal. eapply Int64.same_if_eq. unfold Int64.eq.
      do 2 rewrite Int64.unsigned_repr_eq. rewrite Ptrofs.unsigned_repr_eq. rewrite Ptrofs.modulus_eq64; eauto.
      rewrite Z.mod_mod; [des_ifs|]. specialize Int64.modulus_pos. lia.
    (* int ptr *)
    + unfold to_ptr_val, to_int_val. simpl. rewrite BIT. simpl.
      destruct (Int64.eq i Int64.zero) eqn: NULL; simpl; eauto.
      destruct (Mem.denormalize (Int64.unsigned i) m) eqn:DENO1; simpl; [|auto]. destruct p. simpl.
      rewrite BIT. destruct (eq_block b0 b); [|auto]. subst.
      destruct (Mem.ptr2int b (Ptrofs.unsigned i0) m) eqn:I2P; simpl; [|auto].
      right. right. eapply Mem.denormalize_info in DENO1. des.
      unfold Mem.ptr2int in I2P. rewrite CONC in I2P. subst. inv I2P.
      f_equal. unfold Int64.sub, Ptrofs.sub, Ptrofs.to_int64.
      do 2 rewrite Ptrofs.unsigned_repr_eq. eapply Int64.same_if_eq. unfold Int64.eq.
      do 3 rewrite Int64.unsigned_repr_eq. rewrite Zminus_mod_idemp_l. rewrite Zminus_mod_idemp_r.
      rewrite Ptrofs.modulus_eq64; eauto.
      replace (Int64.unsigned i - (caddr + Ptrofs.unsigned i0)) with (Int64.unsigned i - caddr - Ptrofs.unsigned i0) by lia.
      rewrite Z.mod_mod; [des_ifs|]. specialize Int64.modulus_pos. lia.
  - destruct v2; simpl in *; subst; try rewrite BIT; [auto | auto | | auto | auto | ].
    (* ptr int *)
    + unfold to_ptr_val, to_int_val. simpl. rewrite BIT. simpl.
      destruct (Int64.eq i0 Int64.zero) eqn: NULL; simpl; eauto.
      destruct (Mem.denormalize (Int64.unsigned i0) m) eqn:DENO2; simpl; [|auto]. destruct p. simpl.
      destruct (eq_block b b0); [|auto]. symmetry in e. subst.
      destruct (Mem.ptr2int b (Ptrofs.unsigned i) m) eqn:I2P; simpl; [|auto]. rewrite BIT.
      right. right. eapply Mem.denormalize_info in DENO2. des.
      unfold Mem.ptr2int in I2P. rewrite CONC in I2P. subst. inv I2P.
      f_equal. unfold Int64.sub, Ptrofs.sub, Ptrofs.to_int64.
      do 2 rewrite Ptrofs.unsigned_repr_eq. eapply Int64.same_if_eq. unfold Int64.eq.
      do 3 rewrite Int64.unsigned_repr_eq. rewrite Zminus_mod_idemp_l. rewrite Zminus_mod_idemp_r.
      rewrite Ptrofs.modulus_eq64; eauto.
      replace (Ptrofs.unsigned i - (Int64.unsigned i0 - caddr)) with (caddr + Ptrofs.unsigned i - Int64.unsigned i0) by lia.
      rewrite Z.mod_mod; [des_ifs|]. specialize Int64.modulus_pos. lia.
    + destruct (eq_block b b0); [|auto]. unfold to_int_val. simpl. subst b0.
      destruct (Mem.ptr2int b (Ptrofs.unsigned i) m) eqn:P2I; simpl; [|auto].
      destruct (Mem.ptr2int b (Ptrofs.unsigned i0) m) eqn:P2I'; simpl; [|auto]. rewrite BIT.
      unfold Mem.ptr2int in *. destruct ((Mem.mem_concrete m)!b); [|clarify].
      inv P2I; inv P2I'. right. right. simpl. rewrite BIT.
      unfold Int64.sub, Ptrofs.to_int64, Ptrofs.sub. f_equal. eapply Int64.same_if_eq. unfold Int64.eq.
      repeat rewrite Int64.unsigned_repr_eq. rewrite Ptrofs.unsigned_repr_eq. rewrite Ptrofs.modulus_eq64; eauto.
      rewrite Zminus_mod_idemp_l. rewrite Zminus_mod_idemp_r.
      replace (z1 + Ptrofs.unsigned i - (z1 + Ptrofs.unsigned i0)) with (Ptrofs.unsigned i - Ptrofs.unsigned i0) by lia.
      rewrite Z.mod_mod; [des_ifs|]. specialize Int64.modulus_pos. lia.
Qed.

Lemma cmpu_no_angelic m c v1 v2 bp bi
    (CMP1: Val.cmpu_bool (Mem.valid_pointer m) c (to_ptr_val m v1) (to_ptr_val m v2) = Some bp)
    (CMP2: Val.cmpu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2) = Some bi) :
  <<NOANGELIC: bp = bi>>.
Proof.
  destruct (Archi.ptr64) eqn:BIT.
  { unfold Val.cmpu_bool, to_ptr_val, to_int_val in *.
      unfold Mem.to_ptr, Mem.to_int in *. rewrite BIT in *. simpl in *.
      destruct v1; destruct v2; simpl in *; subst; inversion CMP1; inversion CMP2.
      clear H0 H1. rewrite BIT in *. clear BIT. des_ifs. }
  destruct v1; simpl in *; subst; try rewrite BIT; [clarify| | clarify | clarify | clarify | ].
  - destruct v2; simpl in *; subst; try rewrite BIT; [clarify| | clarify | clarify | clarify | ].
    (* int int *)
    + unfold to_ptr_val in *. simpl in *. rewrite BIT in *. simpl in *.
      destruct (Int.eq i Int.zero) eqn: NULL.
      { destruct (Int.eq i0 Int.zero) eqn: NULL'.
        - simpl in *. eapply Int.same_if_eq in NULL, NULL'. subst. clarify.
        - destruct (Mem.denormalize (Int.unsigned i0) m) eqn:DENO2; simpl in *; eauto.
          2:{ inv CMP1. }
          destruct p; simpl in *. (* rewrite BIT in *.  *) (* rewrite Int.eq_true in CMP1. *) simpl in *.
          destruct (Mem.valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z))
                    || Mem.valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z) - 1)) eqn:WVLD.
          2:{ inv CMP1. }
          eapply Int.same_if_eq in NULL. subst.
          rewrite Int.eq_sym in NULL'. inv CMP2. destruct c; simpl in *; inv CMP1; eauto.
          (* rewrite NULL'. ss. *) }
      destruct (Int.eq i0 Int.zero) eqn: NULL'.
      { destruct (Mem.denormalize (Int.unsigned i) m) eqn:DENO; simpl in *; eauto.
        2:{ inv CMP1. }
        destruct p. simpl in *. (* rewrite Int.eq_true in CMP1. simpl in *. *)
        destruct (Mem.valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z))
                  || Mem.valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z) - 1)) eqn:WVLD.
        2:{ des_ifs; clarify. }
        rewrite BIT in *. eapply Int.same_if_eq in NULL'. subst.
        inv CMP2. destruct c; simpl in *; inv CMP1; eauto. (* rewrite NULL. ss. *) }
      destruct (Mem.denormalize (Int.unsigned i) m) eqn:DENO1; simpl in *; [|clarify]. destruct p. simpl in *.
      destruct (Mem.denormalize (Int.unsigned i0) m) eqn:DENO2; simpl in *; [|clarify]. destruct p. simpl in *.
      destruct (eq_block b b0); rewrite BIT in *.
      (* diff block *)
      2:{ assert (Int.eq i i0 = false).
          { assert (BLK1: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (Int.unsigned i) b).
            { eapply Mem.denormalize_info in DENO1. des. subst. eapply Mem.conditions_of_addr_in_block; eauto. }
            assert (BLK2: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (Int.unsigned i0) b0).
            { eapply Mem.denormalize_info in DENO2. des. subst. eapply Mem.conditions_of_addr_in_block; eauto. }
            unfold Int.eq. clear BIT. des_ifs. rewrite e in *. exfalso. eapply n.
            eapply Mem.no_concrete_overlap; eauto. }
          clear BIT. des_ifs. destruct c; ss; rewrite H; clarify. }
      (* same block *)
      subst b0. eapply Ptrofs.modulus_eq32 in BIT; eauto.
      fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z))) in CMP1.
      fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z0))) in CMP1.
      exploit Mem.denormalize_info; try eapply DENO1; eauto. i. des.
      exploit Mem.denormalize_info; try eapply DENO2; eauto. i. des. subst.
      rewrite CONC in CONC0. inv CONC0. do 2 (rewrite Ptrofs.unsigned_repr in CMP1; [|lia]).
      destruct (Mem.weak_valid_pointer m b (Int.unsigned i - caddr0)
                && Mem.weak_valid_pointer m b (Int.unsigned i0 - caddr0)) eqn:WVLD; [|clarify].
      inv CMP1; inv CMP2.
      assert (EQ: Ptrofs.eq (Ptrofs.repr (Int.unsigned i - caddr0)) (Ptrofs.repr (Int.unsigned i0 - caddr0))
                  = Int.eq i i0).
      { unfold Ptrofs.eq, Int.eq. do 2 (rewrite Ptrofs.unsigned_repr; [|lia]). des_ifs; lia. }
      assert (LT: Ptrofs.ltu (Ptrofs.repr (Int.unsigned i - caddr0)) (Ptrofs.repr (Int.unsigned i0 - caddr0))
                  = Int.ltu i i0).
      { unfold Ptrofs.ltu, Int.ltu. do 2 (rewrite Ptrofs.unsigned_repr; [|lia]). des_ifs; lia. }
      eapply lt_eq_cmpu; eauto.
    (* int ptr *)
    + unfold to_ptr_val, to_int_val in *. simpl in *. rewrite BIT in *. simpl in *.
      destruct (Int.eq i Int.zero) eqn: NULL.
      { simpl in *. (* rewrite BIT in *. eapply Int.same_if_eq in NULL. subst. rewrite Int.eq_true in CMP1. *)
        destruct (Mem.ptr2int b (Ptrofs.unsigned i0)) eqn:P2I; simpl in *.
        2:{ inv CMP2. }
        destruct (Mem.valid_pointer m b (Ptrofs.unsigned i0)
                  || Mem.valid_pointer m b (Ptrofs.unsigned i0 - 1)) eqn:WVLD.
        2:{ inv CMP1. }
        eapply Ptrofs.modulus_eq32 in BIT.
        exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|]. i. des.
        assert (Int.eq Int.zero (Int.repr z) = false).
        { inv INRANGE. simpl in *. unfold Int.zero. unfold Int.eq.
          rewrite BIT in *. rewrite Int.unsigned_repr.
          2:{ split. lia. unfold Int.max_unsigned. specialize Int.modulus_gt_one. lia. }
          rewrite Int.unsigned_repr; [| unfold Int.max_unsigned;lia]. des_ifs; subst; lia. }
        inv CMP2. destruct c; simpl in *; inv CMP1; rewrite H; eauto. }
      destruct (Mem.denormalize (Int.unsigned i) m) eqn:DENO1; simpl in *; [|clarify]. destruct p. simpl in *.
      destruct (eq_block b0 b); rewrite BIT in *.
      2:{ eapply Ptrofs.modulus_eq32 in BIT.
          unfold Mem.ptr2int in CMP2.
          destruct (Mem.valid_pointer m b0 (Ptrofs.unsigned (Ptrofs.repr z))
                    && Mem.valid_pointer m b (Ptrofs.unsigned i0)) eqn:VLD; [|clarify].
          destruct ((Mem.mem_concrete m) ! b) eqn:CONCB; simpl in *; [|clarify].
          simpl in *. inv CMP2.
          assert (Int.eq i (Int.repr (z0 + Ptrofs.unsigned i0)) = false).
          { eapply andb_prop in VLD. des. exploit Mem.denormalize_info; eauto. i. des. subst.
            assert (BLK1: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (Int.unsigned i) b0).
            { eapply Mem.conditions_of_addr_in_block; eauto. }
            assert (BLK2: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (z0 + Ptrofs.unsigned i0) b).
            { eapply Mem.conditions_of_addr_in_block; eauto.
              - replace (z0 + Ptrofs.unsigned i0 - z0) with (Ptrofs.unsigned i0) by lia.
                eapply Mem.perm_cur_max. rewrite <- Mem.valid_pointer_nonempty_perm. eauto.
              - replace (z0 + Ptrofs.unsigned i0 - z0) with (Ptrofs.unsigned i0) by lia.
                eapply Ptrofs.unsigned_range_2. }
            exploit Mem._valid_pointer_range; eauto. i. inv H. unfold fst, snd in *.
            rewrite BIT in SND. clear BIT. unfold Int.eq. des_ifs. rewrite e in *. exfalso. eapply n.
            eapply Mem.no_concrete_overlap; eauto. rewrite Int.unsigned_repr; eauto.
            unfold Int.max_unsigned. lia. }
          clear BIT. des_ifs. destruct c; ss; rewrite H; clarify. }
      (* same block *)
      subst b0. eapply Ptrofs.modulus_eq32 in BIT; eauto.
      fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z))) in CMP1.
      fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned i0)) in CMP1.
      destruct (Mem.ptr2int b (Ptrofs.unsigned i0) m) eqn:P2I; simpl in *; inv CMP2.
      destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z))
                && Mem.weak_valid_pointer m b (Ptrofs.unsigned i0)) eqn: WVLD; inv CMP1.
      eapply andb_prop in WVLD. des. exploit Mem.ptr2int_weak_valid'; eauto;[eapply Ptrofs.unsigned_range_2|].
      exploit Mem.denormalize_info; eauto. i. des; subst. inv INRANGE. simpl in *.
      assert (EQ: Ptrofs.eq (Ptrofs.repr (Int.unsigned i - caddr0)) i0 = Int.eq i (Int.repr (caddr + Ptrofs.unsigned i0))).
      { unfold Ptrofs.eq, Int.eq. rewrite Ptrofs.unsigned_repr; [|lia]. rewrite Int.unsigned_repr.
        2:{ unfold Int.max_unsigned. rewrite <- BIT. lia. }
        des_ifs; lia. }
      assert (LT: Ptrofs.ltu (Ptrofs.repr (Int.unsigned i - caddr0)) i0 = Int.ltu i (Int.repr (caddr + Ptrofs.unsigned i0))).
      { unfold Ptrofs.ltu, Int.ltu. rewrite Ptrofs.unsigned_repr; [|lia]. rewrite Int.unsigned_repr.
        2:{ unfold Int.max_unsigned. rewrite <- BIT. lia. }
        des_ifs; lia. }
      eapply lt_eq_cmpu; eauto.
  - destruct v2; simpl in *; subst; try rewrite BIT; [clarify| | clarify | clarify | clarify | ].
    + unfold to_ptr_val, to_int_val in *. simpl in *. rewrite BIT in *. simpl in *.
      destruct (Int.eq i0 Int.zero) eqn: NULL.
      { simpl in *. eapply Int.same_if_eq in NULL. subst. (* rewrite Int.eq_true in CMP1. *)
        destruct (Mem.ptr2int b (Ptrofs.unsigned i)) eqn:P2I; simpl in *.
        2:{ inv CMP2. }
        destruct (Mem.valid_pointer m b (Ptrofs.unsigned i)
                  || Mem.valid_pointer m b (Ptrofs.unsigned i - 1)) eqn:WVLD.
        2:{ inv CMP1. }
        eapply Ptrofs.modulus_eq32 in BIT.
        exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|]. i. des.
        assert (Int.eq Int.zero (Int.repr z) = false).
        { inv INRANGE. simpl in *. unfold Int.zero. unfold Int.eq.
          rewrite BIT in *. rewrite Int.unsigned_repr.
          2:{ split. lia. unfold Int.max_unsigned. specialize Int.modulus_gt_one. lia. }
          rewrite Int.unsigned_repr; [| unfold Int.max_unsigned;lia]. des_ifs; subst; lia. }
        rewrite Int.eq_sym in H. inv CMP2. destruct c; simpl in *; inv CMP1; rewrite H; eauto. }
      destruct (Mem.denormalize (Int.unsigned i0) m) eqn:DENO2; simpl in *; [|clarify]. destruct p. simpl in *.
      destruct (eq_block b b0); try rewrite BIT in *.
      2:{ eapply Ptrofs.modulus_eq32 in BIT.
          unfold Mem.ptr2int in CMP2.
          destruct (Mem.valid_pointer m b (Ptrofs.unsigned i)
                    && Mem.valid_pointer m b0 (Ptrofs.unsigned (Ptrofs.repr z))) eqn:VLD; [|clarify].
          destruct ((Mem.mem_concrete m) ! b) eqn:CONCB; simpl in *; [|clarify].
          simpl in *. inv CMP2.
          assert (Int.eq (Int.repr (z0 + Ptrofs.unsigned i)) i0 = false).
          { eapply andb_prop in VLD. des. exploit Mem.denormalize_info; eauto. i. des. subst.
            assert (BLK1: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (Int.unsigned i0) b0).
            { eapply Mem.conditions_of_addr_in_block; eauto. }
            assert (BLK2: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (z0 + Ptrofs.unsigned i) b).
            { eapply Mem.conditions_of_addr_in_block; eauto.
              - replace (z0 + Ptrofs.unsigned i - z0) with (Ptrofs.unsigned i) by lia.
                eapply Mem.perm_cur_max. rewrite <- Mem.valid_pointer_nonempty_perm. eauto.
              - replace (z0 + Ptrofs.unsigned i - z0) with (Ptrofs.unsigned i) by lia.
                eapply Ptrofs.unsigned_range_2. }
            exploit Mem._valid_pointer_range; eauto. i. inv H. unfold fst, snd in *.
            rewrite BIT in SND. clear BIT. unfold Int.eq. des_ifs. rewrite <- e in *. exfalso. eapply n.
            eapply Mem.no_concrete_overlap; eauto. rewrite Int.unsigned_repr in BLK1; eauto.
            unfold Int.max_unsigned. lia. }
          clear BIT. des_ifs. destruct c; ss; rewrite H; clarify. }
      (* same block *)
      subst b0. eapply Ptrofs.modulus_eq32 in BIT; eauto.
      fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z))) in CMP1.
      fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)) in CMP1.
      destruct (Mem.ptr2int b (Ptrofs.unsigned i) m) eqn:P2I; simpl in *; inv CMP2.
      destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)
                && Mem.weak_valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z))) eqn: WVLD; inv CMP1.
      eapply andb_prop in WVLD. des. exploit Mem.ptr2int_weak_valid'; eauto;[eapply Ptrofs.unsigned_range_2|].
      exploit Mem.denormalize_info; eauto. i. des; subst. inv INRANGE. simpl in *.
      assert (EQ: Ptrofs.eq i (Ptrofs.repr (Int.unsigned i0 - caddr0)) = Int.eq (Int.repr (caddr + Ptrofs.unsigned i)) i0).
      { unfold Ptrofs.eq, Int.eq. rewrite Ptrofs.unsigned_repr; [|lia]. rewrite Int.unsigned_repr.
        2:{ unfold Int.max_unsigned. rewrite <- BIT. lia. }
        des_ifs; lia. }
      assert (LT: Ptrofs.ltu i (Ptrofs.repr (Int.unsigned i0 - caddr0)) = Int.ltu (Int.repr (caddr + Ptrofs.unsigned i)) i0).
      { unfold Ptrofs.ltu, Int.ltu. rewrite Ptrofs.unsigned_repr; [|lia]. rewrite Int.unsigned_repr.
        2:{ unfold Int.max_unsigned. rewrite <- BIT. lia. }
        des_ifs; lia. }
      eapply lt_eq_cmpu; eauto.
    + unfold to_int_val, Mem.to_int in *. simpl in *. rewrite BIT in *.
      destruct (eq_block b b0).
      2:{ destruct (Mem.valid_pointer m b (Ptrofs.unsigned i)
                    && Mem.valid_pointer m b0 (Ptrofs.unsigned i0)) eqn:VLD; inv CMP1.
          destruct (Mem.ptr2int b (Ptrofs.unsigned i) m) eqn:P2I; simpl in *;[|clarify].
          destruct (Mem.ptr2int b0 (Ptrofs.unsigned i0) m) eqn:P2I'; simpl in *;[|clarify].
          inv CMP2. eapply andb_prop in VLD. des.
          exploit Mem.ptr2int_to_denormalize; try eapply P2I; eauto.
          { eapply Ptrofs.unsigned_range_2. }
          exploit Mem.ptr2int_to_denormalize; try eapply P2I'; eauto.
          { eapply Ptrofs.unsigned_range_2. }
          i. des. exploit Mem.denormalize_info; try eapply H; eauto. exploit Mem.denormalize_info; try eapply H0; eauto.
          i. des. subst.
          assert (Int.eq (Int.repr z) (Int.repr z0) = false).
          { assert (BLK1: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) z0 b0).
            { eapply Mem.conditions_of_addr_in_block; eauto.
              - rewrite <- OFS. eauto.
              - rewrite <- OFS. eapply Ptrofs.unsigned_range_2. }
            assert (BLK2: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) z b).
            { eapply Mem.conditions_of_addr_in_block; eauto.
              - rewrite <- OFS0. eauto.
              - rewrite <- OFS0. eapply Ptrofs.unsigned_range_2. }
            exploit Mem._valid_pointer_range; eauto. i. inv H2. unfold fst, snd in *.
            eapply Ptrofs.modulus_eq32 in BIT. rewrite BIT in *.
            unfold Int.eq. rewrite Int.unsigned_repr.
            2:{ unfold Int.max_unsigned. lia. }
            rewrite Int.unsigned_repr.
            2:{ unfold Int.max_unsigned, Ptrofs.max_unsigned in *. rewrite <- BIT. lia. }
            destruct (zeq z z0); eauto. exfalso. subst. eapply n. eapply Mem.no_concrete_overlap; eauto. }
          clear BIT. des_ifs. destruct c; ss; rewrite H2; clarify. }
      { subst b0. eapply Ptrofs.modulus_eq32 in BIT; eauto.
        fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned i0)) in CMP1.
        fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)) in CMP1.
        destruct (Mem.ptr2int b (Ptrofs.unsigned i) m) eqn:P2I; simpl in *; inv CMP2.
        destruct (Mem.ptr2int b (Ptrofs.unsigned i0) m) eqn:P2I'; simpl in *; inv H0.
        destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)
                  && Mem.weak_valid_pointer m b (Ptrofs.unsigned i0)) eqn:WVLD; inv CMP1.
        eapply andb_prop in WVLD. des.
        exploit Mem.ptr2int_weak_valid'; try eapply P2I; eauto;[eapply Ptrofs.unsigned_range_2|].
        exploit Mem.ptr2int_weak_valid'; try eapply P2I'; eauto;[eapply Ptrofs.unsigned_range_2|].
        i. des. subst. inv INRANGE; inv INRANGE0. simpl in *. rewrite CONC in CONC0. inv CONC0.
        assert (EQ: Ptrofs.eq i i0 = Int.eq (Int.repr (caddr0 + Ptrofs.unsigned i)) (Int.repr (caddr0 + Ptrofs.unsigned i0))).
        { unfold Ptrofs.eq, Int.eq. rewrite BIT in *. do 2 (rewrite Int.unsigned_repr; [|unfold Int.max_unsigned; lia]).
          des_ifs; lia. }
        assert (LT: Ptrofs.ltu i i0 = Int.ltu (Int.repr (caddr0 + Ptrofs.unsigned i)) (Int.repr (caddr0 + Ptrofs.unsigned i0))).
        { unfold Ptrofs.ltu, Int.ltu. rewrite BIT in *. do 2 (rewrite Int.unsigned_repr; [|unfold Int.max_unsigned; lia]).
          des_ifs; lia. }
        eapply lt_eq_cmpu; eauto. }
Qed.

Lemma cmpu_no_angelic' m c v1 v2 vp vi
    (CMP1: Val.cmpu (Mem.valid_pointer m) c (to_ptr_val m v1) (to_ptr_val m v2) = vp)
    (CMP2: Val.cmpu (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2) = vi) :
  <<NOANGELIC: vp = Vundef \/ vi = Vundef \/ vp = vi>>.
Proof.
  unfold Val.cmpu in *. unfold Val.of_optbool in *. des_ifs; eauto; exploit cmpu_no_angelic; eauto; clarify.
Qed.

Lemma cmplu_no_angelic m c v1 v2 bp bi
    (CMP1: Val.cmplu_bool (Mem.valid_pointer m) c (to_ptr_val m v1) (to_ptr_val m v2) = Some bp)
    (CMP2: Val.cmplu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2) = Some bi) :
  <<NOANGELIC: bp = bi>>.
Proof.
  destruct (Archi.ptr64) eqn:BIT.
  2:{ unfold Val.cmplu_bool, to_ptr_val, to_int_val in *.
      unfold Mem.to_ptr, Mem.to_int in *. rewrite BIT in *. simpl in *.
      destruct v1; destruct v2; simpl in *; subst; inversion CMP1; inversion CMP2.
      clear H0 H1. rewrite BIT in *. clear BIT. des_ifs. }
  destruct v1; simpl in *; subst; try rewrite BIT; [clarify|clarify| |clarify|clarify|].
  - destruct v2; simpl in *; subst; try rewrite BIT; [clarify|clarify| |clarify|clarify|].
    (* int int *)
    + unfold to_ptr_val in *. simpl in *. rewrite BIT in *. simpl in *.
      destruct (Int64.eq i Int64.zero) eqn: NULL.
      { destruct (Int64.eq i0 Int64.zero) eqn: NULL'.
        - simpl in *. eapply Int64.same_if_eq in NULL, NULL'. subst.
          unfold Val.cmplu_bool in CMP1. unfold Vnullptr in *. des_ifs.
        - destruct (Mem.denormalize (Int64.unsigned i0) m) eqn:DENO2; simpl in *; eauto.
          2:{ inv CMP1. }
          destruct p; unfold Val.cmplu_bool, Vnullptr in *; simpl in *. rewrite BIT in *. ss.
          rewrite Int64.eq_true in CMP1.
          (* simpl in *. *)
          destruct (Mem.valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z))
                    || Mem.valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z) - 1)) eqn:WVLD.
          2:{ inv CMP1. }
          eapply Int64.same_if_eq in NULL. subst.
          rewrite Int64.eq_sym in NULL'. inv CMP2. destruct c; simpl in *; inv CMP1; eauto.
          rewrite NULL'. ss. }
      destruct (Int64.eq i0 Int64.zero) eqn: NULL'.
      { destruct (Mem.denormalize (Int64.unsigned i) m) eqn:DENO; simpl in *; eauto.
        2:{ inv CMP1. }
        destruct p. unfold Val.cmplu_bool, Vnullptr in CMP1. simpl in *. rewrite BIT in *.
        rewrite Int64.eq_true in CMP1. simpl in *.
        destruct (Mem.valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z))
                  || Mem.valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z) - 1)) eqn:WVLD.
        2:{ des_ifs; clarify. }
        eapply Int64.same_if_eq in NULL'. subst.
        inv CMP2. destruct c; simpl in *; inv CMP1; eauto. rewrite NULL. ss. }
      destruct (Mem.denormalize (Int64.unsigned i) m) eqn:DENO1; simpl in *; [|clarify]. destruct p. simpl in *.
      destruct (Mem.denormalize (Int64.unsigned i0) m) eqn:DENO2; simpl in *; [|clarify]. destruct p. simpl in *.
      destruct (eq_block b b0); rewrite BIT in *.
      (* diff block *)
      2:{ assert (Int64.eq i i0 = false).
          { assert (BLK1: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (Int64.unsigned i) b).
            { eapply Mem.denormalize_info in DENO1. des. subst. eapply Mem.conditions_of_addr_in_block; eauto. }
            assert (BLK2: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (Int64.unsigned i0) b0).
            { eapply Mem.denormalize_info in DENO2. des. subst. eapply Mem.conditions_of_addr_in_block; eauto. }
            unfold Int64.eq. clear BIT. des_ifs. rewrite e in *. exfalso. eapply n.
            eapply Mem.no_concrete_overlap; eauto. }
          clear BIT. des_ifs. destruct c; ss; rewrite H; clarify. }
      (* same block *)
      subst b0. eapply Ptrofs.modulus_eq64 in BIT; eauto.
      fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z))) in CMP1.
      fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z0))) in CMP1.
      exploit Mem.denormalize_info; try eapply DENO1; eauto. i. des.
      exploit Mem.denormalize_info; try eapply DENO2; eauto. i. des. subst.
      rewrite CONC in CONC0. inv CONC0. do 2 (rewrite Ptrofs.unsigned_repr in CMP1; [|lia]).
      destruct (Mem.weak_valid_pointer m b (Int64.unsigned i - caddr0)
                && Mem.weak_valid_pointer m b (Int64.unsigned i0 - caddr0)) eqn:WVLD; [|clarify].
      inv CMP1; inv CMP2.
      assert (EQ: Ptrofs.eq (Ptrofs.repr (Int64.unsigned i - caddr0)) (Ptrofs.repr (Int64.unsigned i0 - caddr0))
                  = Int64.eq i i0).
      { unfold Ptrofs.eq, Int64.eq. do 2 (rewrite Ptrofs.unsigned_repr; [|lia]). des_ifs; lia. }
      assert (LT: Ptrofs.ltu (Ptrofs.repr (Int64.unsigned i - caddr0)) (Ptrofs.repr (Int64.unsigned i0 - caddr0))
                  = Int64.ltu i i0).
      { unfold Ptrofs.ltu, Int64.ltu. do 2 (rewrite Ptrofs.unsigned_repr; [|lia]). des_ifs; lia. }
      eapply lt_eq_cmplu; eauto.
    (* int ptr *)
    + unfold to_ptr_val, to_int_val in *. simpl in *. rewrite BIT in *. simpl in *.
      destruct (Int64.eq i Int64.zero) eqn: NULL.
      { unfold Val.cmplu_bool, Vnullptr in *. simpl in *. rewrite BIT in *. eapply Int64.same_if_eq in NULL.
        subst. rewrite Int64.eq_true in CMP1.
        destruct (Mem.ptr2int b (Ptrofs.unsigned i0)) eqn:P2I; simpl in *.
        2:{ inv CMP2. }
        destruct (Mem.valid_pointer m b (Ptrofs.unsigned i0)
                  || Mem.valid_pointer m b (Ptrofs.unsigned i0 - 1)) eqn:WVLD.
        2:{ inv CMP1. }
        eapply Ptrofs.modulus_eq64 in BIT.
        exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|]. i. des.
        assert (Int64.eq Int64.zero (Int64.repr z) = false).
        { inv INRANGE. simpl in *. unfold Int64.zero. unfold Int64.eq.
          rewrite BIT in *. rewrite Int64.unsigned_repr.
          2:{ split. lia. unfold Int64.max_unsigned. specialize Int64.modulus_gt_one. lia. }
          rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned;lia]. des_ifs; subst; lia. }
        inv CMP2. destruct c; simpl in *; inv CMP1; rewrite H; eauto. }
      destruct (Mem.denormalize (Int64.unsigned i) m) eqn:DENO1; simpl in *; [|clarify]. destruct p. simpl in *.
      destruct (eq_block b0 b); rewrite BIT in *.
      2:{ eapply Ptrofs.modulus_eq64 in BIT.
          unfold Mem.ptr2int in CMP2.
          destruct (Mem.valid_pointer m b0 (Ptrofs.unsigned (Ptrofs.repr z))
                    && Mem.valid_pointer m b (Ptrofs.unsigned i0)) eqn:VLD; [|clarify].
          destruct ((Mem.mem_concrete m) ! b) eqn:CONCB; simpl in *; [|clarify].
          simpl in *. inv CMP2.
          assert (Int64.eq i (Int64.repr (z0 + Ptrofs.unsigned i0)) = false).
          { eapply andb_prop in VLD. des. exploit Mem.denormalize_info; eauto. i. des. subst.
            assert (BLK1: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (Int64.unsigned i) b0).
            { eapply Mem.conditions_of_addr_in_block; eauto. }
            assert (BLK2: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (z0 + Ptrofs.unsigned i0) b).
            { eapply Mem.conditions_of_addr_in_block; eauto.
              - replace (z0 + Ptrofs.unsigned i0 - z0) with (Ptrofs.unsigned i0) by lia.
                eapply Mem.perm_cur_max. rewrite <- Mem.valid_pointer_nonempty_perm. eauto.
              - replace (z0 + Ptrofs.unsigned i0 - z0) with (Ptrofs.unsigned i0) by lia.
                eapply Ptrofs.unsigned_range_2. }
            exploit Mem._valid_pointer_range; eauto. i. inv H. unfold fst, snd in *.
            rewrite BIT in SND. clear BIT. unfold Int64.eq. des_ifs. rewrite e in *. exfalso. eapply n.
            eapply Mem.no_concrete_overlap; eauto. rewrite Int64.unsigned_repr; eauto.
            unfold Int64.max_unsigned. lia. }
          clear BIT. des_ifs. destruct c; ss; rewrite H; clarify. }
      (* same block *)
      subst b0. eapply Ptrofs.modulus_eq64 in BIT; eauto.
      fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z))) in CMP1.
      fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned i0)) in CMP1.
      destruct (Mem.ptr2int b (Ptrofs.unsigned i0) m) eqn:P2I; simpl in *; inv CMP2.
      destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z))
                && Mem.weak_valid_pointer m b (Ptrofs.unsigned i0)) eqn: WVLD; inv CMP1.
      eapply andb_prop in WVLD. des. exploit Mem.ptr2int_weak_valid'; eauto;[eapply Ptrofs.unsigned_range_2|].
      exploit Mem.denormalize_info; eauto. i. des; subst. inv INRANGE. simpl in *.
      assert (EQ: Ptrofs.eq (Ptrofs.repr (Int64.unsigned i - caddr0)) i0 = Int64.eq i (Int64.repr (caddr + Ptrofs.unsigned i0))).
      { unfold Ptrofs.eq, Int64.eq. rewrite Ptrofs.unsigned_repr; [|lia]. rewrite Int64.unsigned_repr.
        2:{ unfold Int64.max_unsigned. rewrite <- BIT. lia. }
        des_ifs; lia. }
      assert (LT: Ptrofs.ltu (Ptrofs.repr (Int64.unsigned i - caddr0)) i0 = Int64.ltu i (Int64.repr (caddr + Ptrofs.unsigned i0))).
      { unfold Ptrofs.ltu, Int64.ltu. rewrite Ptrofs.unsigned_repr; [|lia]. rewrite Int64.unsigned_repr.
        2:{ unfold Int64.max_unsigned. rewrite <- BIT. lia. }
        des_ifs; lia. }
      eapply lt_eq_cmplu; eauto.
  - destruct v2; simpl in *; subst; try rewrite BIT; [clarify|clarify| |clarify|clarify| ].
    + unfold to_ptr_val, to_int_val in *. simpl in *. rewrite BIT in *. simpl in *.
      destruct (Int64.eq i0 Int64.zero) eqn: NULL.
      { unfold Vnullptr, Val.cmplu_bool in *.
        simpl in *. eapply Int64.same_if_eq in NULL. rewrite BIT in *. subst. rewrite Int64.eq_true in CMP1.
        destruct (Mem.ptr2int b (Ptrofs.unsigned i)) eqn:P2I; simpl in *.
        2:{ inv CMP2. }
        destruct (Mem.valid_pointer m b (Ptrofs.unsigned i)
                  || Mem.valid_pointer m b (Ptrofs.unsigned i - 1)) eqn:WVLD.
        2:{ inv CMP1. }
        eapply Ptrofs.modulus_eq64 in BIT.
        exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|]. i. des.
        assert (Int64.eq Int64.zero (Int64.repr z) = false).
        { inv INRANGE. simpl in *. unfold Int64.zero. unfold Int64.eq.
          rewrite BIT in *. rewrite Int64.unsigned_repr.
          2:{ split. lia. unfold Int64.max_unsigned. specialize Int64.modulus_gt_one. lia. }
          rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned;lia]. des_ifs; subst; lia. }
        rewrite Int64.eq_sym in H. inv CMP2. destruct c; simpl in *; inv CMP1; rewrite H; eauto. }
      destruct (Mem.denormalize (Int64.unsigned i0) m) eqn:DENO2; simpl in *; [|clarify]. destruct p. simpl in *.
      destruct (eq_block b b0); try rewrite BIT in *.
      2:{ eapply Ptrofs.modulus_eq64 in BIT.
          unfold Mem.ptr2int in CMP2.
          destruct (Mem.valid_pointer m b (Ptrofs.unsigned i)
                    && Mem.valid_pointer m b0 (Ptrofs.unsigned (Ptrofs.repr z))) eqn:VLD; [|clarify].
          destruct ((Mem.mem_concrete m) ! b) eqn:CONCB; simpl in *; [|clarify].
          simpl in *. inv CMP2.
          assert (Int64.eq (Int64.repr (z0 + Ptrofs.unsigned i)) i0 = false).
          { eapply andb_prop in VLD. des. exploit Mem.denormalize_info; eauto. i. des. subst.
            assert (BLK1: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (Int64.unsigned i0) b0).
            { eapply Mem.conditions_of_addr_in_block; eauto. }
            assert (BLK2: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (z0 + Ptrofs.unsigned i) b).
            { eapply Mem.conditions_of_addr_in_block; eauto.
              - replace (z0 + Ptrofs.unsigned i - z0) with (Ptrofs.unsigned i) by lia.
                eapply Mem.perm_cur_max. rewrite <- Mem.valid_pointer_nonempty_perm. eauto.
              - replace (z0 + Ptrofs.unsigned i - z0) with (Ptrofs.unsigned i) by lia.
                eapply Ptrofs.unsigned_range_2. }
            exploit Mem._valid_pointer_range; eauto. i. inv H. unfold fst, snd in *.
            rewrite BIT in SND. clear BIT. unfold Int64.eq. des_ifs. rewrite <- e in *. exfalso. eapply n.
            eapply Mem.no_concrete_overlap; eauto. rewrite Int64.unsigned_repr in BLK1; eauto.
            unfold Int64.max_unsigned. lia. }
          clear BIT. des_ifs. destruct c; ss; rewrite H; clarify. }
      (* same block *)
      subst b0. eapply Ptrofs.modulus_eq64 in BIT; eauto.
      fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z))) in CMP1.
      fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)) in CMP1.
      destruct (Mem.ptr2int b (Ptrofs.unsigned i) m) eqn:P2I; simpl in *; inv CMP2.
      destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)
                && Mem.weak_valid_pointer m b (Ptrofs.unsigned (Ptrofs.repr z))) eqn: WVLD; inv CMP1.
      eapply andb_prop in WVLD. des. exploit Mem.ptr2int_weak_valid'; eauto;[eapply Ptrofs.unsigned_range_2|].
      exploit Mem.denormalize_info; eauto. i. des; subst. inv INRANGE. simpl in *.
      assert (EQ: Ptrofs.eq i (Ptrofs.repr (Int64.unsigned i0 - caddr0)) = Int64.eq (Int64.repr (caddr + Ptrofs.unsigned i)) i0).
      { unfold Ptrofs.eq, Int64.eq. rewrite Ptrofs.unsigned_repr; [|lia]. rewrite Int64.unsigned_repr.
        2:{ unfold Int64.max_unsigned. rewrite <- BIT. lia. }
        des_ifs; lia. }
      assert (LT: Ptrofs.ltu i (Ptrofs.repr (Int64.unsigned i0 - caddr0)) = Int64.ltu (Int64.repr (caddr + Ptrofs.unsigned i)) i0).
      { unfold Ptrofs.ltu, Int64.ltu. rewrite Ptrofs.unsigned_repr; [|lia]. rewrite Int64.unsigned_repr.
        2:{ unfold Int64.max_unsigned. rewrite <- BIT. lia. }
        des_ifs; lia. }
      eapply lt_eq_cmplu; eauto.
    + unfold to_int_val, Mem.to_int in *. simpl in *. rewrite BIT in *.
      destruct (eq_block b b0).
      2:{ destruct (Mem.valid_pointer m b (Ptrofs.unsigned i)
                    && Mem.valid_pointer m b0 (Ptrofs.unsigned i0)) eqn:VLD; inv CMP1.
          destruct (Mem.ptr2int b (Ptrofs.unsigned i) m) eqn:P2I; simpl in *;[|clarify].
          destruct (Mem.ptr2int b0 (Ptrofs.unsigned i0) m) eqn:P2I'; simpl in *;[|clarify].
          inv CMP2. eapply andb_prop in VLD. des.
          exploit Mem.ptr2int_to_denormalize; try eapply P2I; eauto.
          { eapply Ptrofs.unsigned_range_2. }
          exploit Mem.ptr2int_to_denormalize; try eapply P2I'; eauto.
          { eapply Ptrofs.unsigned_range_2. }
          i. des. exploit Mem.denormalize_info; try eapply H; eauto. exploit Mem.denormalize_info; try eapply H0; eauto.
          i. des. subst.
          assert (Int64.eq (Int64.repr z) (Int64.repr z0) = false).
          { assert (BLK1: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) z0 b0).
            { eapply Mem.conditions_of_addr_in_block; eauto.
              - rewrite <- OFS. eauto.
              - rewrite <- OFS. eapply Ptrofs.unsigned_range_2. }
            assert (BLK2: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) z b).
            { eapply Mem.conditions_of_addr_in_block; eauto.
              - rewrite <- OFS0. eauto.
              - rewrite <- OFS0. eapply Ptrofs.unsigned_range_2. }
            exploit Mem._valid_pointer_range; eauto. i. inv H2. unfold fst, snd in *.
            eapply Ptrofs.modulus_eq64 in BIT. rewrite BIT in *.
            unfold Int64.eq. rewrite Int64.unsigned_repr.
            2:{ unfold Int64.max_unsigned. lia. }
            rewrite Int64.unsigned_repr.
            2:{ unfold Int64.max_unsigned, Ptrofs.max_unsigned in *. rewrite <- BIT. lia. }
            destruct (zeq z z0); eauto. exfalso. subst. eapply n. eapply Mem.no_concrete_overlap; eauto. }
          clear BIT. des_ifs. destruct c; ss; rewrite H2; clarify. }
      { subst b0. eapply Ptrofs.modulus_eq64 in BIT; eauto.
        fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned i0)) in CMP1.
        fold (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)) in CMP1.
        destruct (Mem.ptr2int b (Ptrofs.unsigned i) m) eqn:P2I; simpl in *; inv CMP2.
        destruct (Mem.ptr2int b (Ptrofs.unsigned i0) m) eqn:P2I'; simpl in *; inv H0.
        destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)
                  && Mem.weak_valid_pointer m b (Ptrofs.unsigned i0)) eqn:WVLD; inv CMP1.
        eapply andb_prop in WVLD. des.
        exploit Mem.ptr2int_weak_valid'; try eapply P2I; eauto;[eapply Ptrofs.unsigned_range_2|].
        exploit Mem.ptr2int_weak_valid'; try eapply P2I'; eauto;[eapply Ptrofs.unsigned_range_2|].
        i. des. subst. inv INRANGE; inv INRANGE0. simpl in *. rewrite CONC in CONC0. inv CONC0.
        assert (EQ: Ptrofs.eq i i0 = Int64.eq (Int64.repr (caddr0 + Ptrofs.unsigned i)) (Int64.repr (caddr0 + Ptrofs.unsigned i0))).
        { unfold Ptrofs.eq, Int64.eq. rewrite BIT in *. do 2 (rewrite Int64.unsigned_repr; [|unfold Int64.max_unsigned; lia]).
          des_ifs; lia. }
        assert (LT: Ptrofs.ltu i i0 = Int64.ltu (Int64.repr (caddr0 + Ptrofs.unsigned i)) (Int64.repr (caddr0 + Ptrofs.unsigned i0))).
        { unfold Ptrofs.ltu, Int64.ltu. rewrite BIT in *. do 2 (rewrite Int64.unsigned_repr; [|unfold Int64.max_unsigned; lia]).
          des_ifs; lia. }
        eapply lt_eq_cmplu; eauto. }
Qed.

Lemma cmplu_no_angelic' m c v1 v2 vp vi
    (CMP1: Val.cmplu (Mem.valid_pointer m) c (to_ptr_val m v1) (to_ptr_val m v2) = Some vp)
    (CMP2: Val.cmplu (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2) = Some vi) :
  <<NOANGELIC: vp = vi>>.
Proof.
  unfold Val.cmplu in *. unfold option_map, Val.of_bool in *. des_ifs; eauto; exploit cmplu_no_angelic; eauto; clarify.
Qed.

Definition is_only_int (v: val) : bool :=
  match v with
  | Vundef | Vint _ | Vlong _ => true | _ => false
  end.

Lemma psub_is_only_int v1 v2 : <<ONLYINT: is_only_int (Val.psub v1 v2) = true>>.
Proof. unfold Val.psub. des_ifs. Qed.

Lemma psubl_is_only_int v1 v2 : <<ONLYINT: is_only_int (Val.psubl v1 v2) = true>>.
Proof. unfold Val.psubl. des_ifs. Qed.

Lemma cmpu_is_only_int m c v1 v2 :
  <<ONLYINT: is_only_int (Val.cmpu (Mem.valid_pointer m) c v1 v2) = true>>.
Proof. unfold Val.cmpu, Val.of_bool, Val.of_optbool. des_ifs. Qed.

Lemma cmplu_is_only_int m c v1 v2 v
    (CMP: Val.cmplu (Mem.valid_pointer m) c v1 v2 = Some v) :
  <<ONLYINT: is_only_int v = true >>.
Proof. unfold Val.cmplu, Val.of_bool, Val.of_optbool, option_map in *. des_ifs. Qed.

Definition val_join (v1 v2: val) : val :=
  match v1, v2 with
  | Vundef, _ => v2 | _, Vundef => v1
  | Vint n1, Vint n2 => if Int.eq n1 n2 then Vint n1 else Vundef
  | Vlong n1, Vlong n2 => if Int64.eq n1 n2 then Vlong n1 else Vundef
  | _, _ => Vundef
  end.

Lemma val_join_same_val v
    (IRET: is_only_int v = true) :        
  <<SAME: val_join v v = v>>.
Proof. destruct v; ss; [rewrite Int.eq_true|rewrite Int64.eq_true]; eauto. Qed.

Lemma val_join_angelic_vp vp vi
    (ISINT: is_only_int vp = true)
    (NOANGELIC: vp = Vundef \/ vi = Vundef \/ vi = vp)
    (SUCCSS: vp <> Vundef) :
  <<VAL: val_join vp vi = vp>>.
Proof.
  des; subst; clarify; unfold val_join; des_ifs.
  - rewrite Int.eq_true in Heq. clarify.
  - rewrite Int64.eq_true in Heq. clarify.
Qed.

Lemma val_join_angelic_vi vp vi
    (ISINT: is_only_int vi = true)
    (NOANGELIC: vp = Vundef \/ vi = Vundef \/ vi = vp)
    (SUCCSS: vi <> Vundef) :
  <<VAL: val_join vp vi = vi>>.
Proof.
  des; subst; clarify; unfold val_join; des_ifs.
  - rewrite Int.eq_true in Heq. clarify.
  - rewrite Int64.eq_true in Heq. clarify.
Qed.

Definition bool_join (b1 b2: bool) : option bool:= if eqb b1 b2 then Some b1 else None.

Lemma bool_join_angelic b1 b2
    (NOANGELIC: b1 = b2) :
  <<BOOL: bool_join b1 b2 = Some b1>>.
Proof. subst. unfold bool_join. rewrite eqb_reflx. eauto. Qed.

Section OPTJOIN.

Set Implicit Arguments.
Variable R: Type.
Variable rjoin : R -> R -> option R.

Definition opt_join (or1 or2: option R) : option R :=
  match or1, or2 with
  | Some r1, Some r2 => rjoin r1 r2
  | None, Some r2 => Some r2
  | Some r1, None => Some r1
  | _, _ => None
  end.

End OPTJOIN.

Definition val_optjoin (ov1 ov2: option val) : option val :=
  opt_join (fun v1 v2 => Some (val_join v1 v2)) ov1 ov2.

Lemma val_optjoin_same_val v
    (IRET: is_only_int v = true) :
  <<SAME: val_optjoin (Some v) (Some v) = Some v>>.
Proof. unfold val_optjoin. ss. rewrite val_join_same_val; eauto. Qed.

Lemma val_optjoin_angelic_vp vp ovi
    (IRET: is_only_int vp = true)
    (NOANGELIC: ovi = Some vp \/ ovi = Some Vundef \/ ovi = None)
    (SUCCESS: vp <> Vundef) :
  <<SAME: val_optjoin (Some vp) ovi = Some vp>>.
Proof.
  des; subst; ss.
  - rewrite val_join_same_val; eauto.
  - unfold val_join. ss. des_ifs.
Qed.

Lemma val_optjoin_angelic_vi vi ovp
    (IRET: is_only_int vi = true)
    (NOANGELIC: ovp = Some vi \/ ovp = Some Vundef \/ ovp = None)
    (SUCCESS: vi <> Vundef) :
  <<SAME: val_optjoin ovp (Some vi) = Some vi>>.
Proof. des; subst; ss. rewrite val_join_same_val; eauto. Qed.

Definition bool_optjoin (ob1 ob2: option bool) : option bool := opt_join bool_join ob1 ob2.

Lemma bool_optjoin_same_bool b:
  <<SAME: bool_optjoin (Some b) (Some b) = Some b>>.
Proof. destruct b; ss. Qed.

Lemma bool_optjoin_angelic_vp vp ovi
    (NOANGELIC: ovi = Some vp \/ ovi = None) :
  <<SAME: bool_optjoin (Some vp) ovi = Some vp>>.
Proof. des; subst; ss. eapply bool_optjoin_same_bool. Qed.

Lemma bool_optjoin_angelic_vi vi ovp
    (NOANGELIC: ovp = Some vi \/ ovp = None) :
  <<SAME: bool_optjoin ovp (Some vi) = Some vi>>.
Proof. des; subst; ss. eapply bool_optjoin_same_bool. Qed.

(** Pointer Binary Operation Join *)

Section PTRBINJOIN.

Variable m : mem.

Definition psub_join (v1 v2: val) : val :=
  val_join (Val.psub (to_ptr_val m v1) (to_ptr_val m v2)) (Val.psub (to_int_val m v1) (to_int_val m v2)).

Definition psubl_join (v1 v2: val) : val :=
  val_join (Val.psubl (to_ptr_val m v1) (to_ptr_val m v2)) (Val.psubl (to_int_val m v1) (to_int_val m v2)).

Definition cmpu_join (c: comparison) (v1 v2: val) : option bool :=
  bool_optjoin (Val.cmpu_bool (Mem.valid_pointer m) c (to_ptr_val m v1) (to_ptr_val m v2))
               (Val.cmpu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2)).

Definition cmplu_join (c: comparison) (v1 v2: val) : option bool :=
  bool_optjoin (Val.cmplu_bool (Mem.valid_pointer m) c (to_ptr_val m v1) (to_ptr_val m v2))
               (Val.cmplu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2)).

Definition cmpu_join_common (c: comparison) (v1 v2: val) : option bool :=
  match v1, v2 with
  | Vptr _ _, Vptr _ _ | Vint _, Vint _ => Val.cmpu_bool (Mem.valid_pointer m) c v1 v2
  | Vptr _ _, Vint n | Vint n, Vptr _ _ => if Int.eq n Int.zero
                                          then Val.cmpu_bool (Mem.valid_pointer m) c v1 v2
                                          else cmpu_join c v1 v2
  | _, _ => None
  end.

Definition cmplu_join_common (c: comparison) (v1 v2: val) : option bool :=
  match v1, v2 with
  | Vptr _ _, Vptr _ _ | Vlong _, Vlong _ => Val.cmplu_bool (Mem.valid_pointer m) c v1 v2
  | Vptr _ _, Vlong n | Vlong n, Vptr _ _ => if Int64.eq n Int64.zero
                                            then Val.cmplu_bool (Mem.valid_pointer m) c v1 v2
                                            else cmplu_join c v1 v2
  | _, _ => None
  end.

(* Definition cmpu_join' (c: comparison) (v1 v2: val) : val := *)
(*   val_join (Val.cmpu (Mem.valid_pointer m) c (to_ptr_val m v1) (to_ptr_val m v2)) *)
(*            (Val.cmpu (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2)). *)

(* Definition cmplu_join' (c: comparison) (v1 v2: val) : option val := *)
(*   val_optjoin (Val.cmplu (Mem.valid_pointer m) c (to_ptr_val m v1) (to_ptr_val m v2)) *)
(*               (Val.cmplu (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2)). *)

Lemma to_ptr_val_add_comm_l1 b ofs n:
  to_ptr_val m (Val.addl (Vptr b ofs) n) = Val.addl (to_ptr_val m (Vptr b ofs)) n.
Proof. unfold Val.addl, to_ptr_val; destruct n; simpl; eauto. Qed.

Lemma to_ptr_val_add_comm_l2 b ofs n:
  to_ptr_val m (Val.addl n (Vptr b ofs)) = Val.addl n (to_ptr_val m (Vptr b ofs)).
Proof. unfold Val.addl, to_ptr_val; destruct n; simpl; eauto. Qed.

Lemma psubl_always_captured1 i b ofs n
    (SUCCESS: psubl_join (Vlong i) (Vptr b ofs) = Vlong n) :
  exists caddr, (Mem.mem_concrete m) ! b = Some caddr.
Proof.
  unfold psubl_join in *. unfold val_join in *. des_ifs.
  - unfold Val.psubl in SUCCESS. des_ifs. unfold to_int_val in Heq1. ss. des_ifs.
    unfold Mem.ptr2int in Heq3. des_ifs. eauto.
  - unfold Val.psubl in Heq. des_ifs. unfold to_ptr_val in *. ss. des_ifs_safe.
    ss. inv Heq1. eapply Mem.denormalize_info in Heq4. des; eauto.
  - unfold Val.psubl in Heq0. des_ifs. unfold to_int_val in Heq3. ss. des_ifs.
    unfold Mem.ptr2int in Heq0. des_ifs. eauto.
Qed.

Lemma cmplu_always_captured1 c i b ofs bi
    (NOTEQ: c <> Ceq /\ c <> Cne)
    (NOTNULL: Int64.eq i Int64.zero = false)
    (SUCCESS: cmplu_join c (Vlong i) (Vptr b ofs) = Some bi) :
  exists caddr, (Mem.mem_concrete m) ! b = Some caddr.
Proof.
  unfold cmplu_join in *. unfold bool_optjoin in *.
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_ptr_val m (Vlong i)) (to_ptr_val m (Vptr b ofs))) eqn:CMP1;
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_int_val m (Vlong i)) (to_int_val m (Vptr b ofs))) eqn:CMP2; ss.
  - rewrite NOTNULL in *. ss. des_ifs_safe. unfold to_int_val in Heq. ss. des_ifs.
    unfold Mem.ptr2int in Heq0. des_ifs. eauto.
  - clear CMP2. unfold Val.cmplu_bool in CMP1. des_ifs.
    { unfold to_ptr_val in Heq. ss. des_ifs. }
    { unfold to_ptr_val, Mem.to_ptr in *. des_ifs. ss. clarify.
      eapply Mem.denormalize_info in Heq4. des. eauto. }
    { destruct c; ss; des; clarify. }
  - clear CMP1. rewrite NOTNULL in *. ss. des_ifs_safe. unfold to_int_val in Heq. ss. des_ifs.
    unfold Mem.ptr2int in Heq0. des_ifs. eauto.
Qed.

Lemma cmplu_always_captured1' c i b ofs caddr
    (CAP: (Mem.mem_concrete m) ! b = Some caddr) :
  <<SUCCESS: cmplu_join c (Vlong i) (Vptr b ofs) = Some (Int64.cmpu c i (Int64.repr (caddr + Ptrofs.unsigned ofs)))>>.
Proof.
  unfold cmplu_join.
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_ptr_val m (Vlong i)) (to_ptr_val m (Vptr b ofs))) eqn: CMPP;
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_int_val m (Vlong i)) (to_int_val m (Vptr b ofs))) eqn: CMPI.
  - rewrite bool_optjoin_angelic_vi; eauto.
    { ss. unfold to_int_val in CMPI; ss. unfold Mem.ptr2int in CMPI. des_ifs. ss. inv Heq. eauto. }
    left. f_equal. eapply cmplu_no_angelic; eauto.
  - exfalso. unfold to_int_val in CMPI; ss. unfold Mem.ptr2int in CMPI. des_ifs.
  - rewrite bool_optjoin_angelic_vi; eauto.
    unfold to_int_val in CMPI; ss. unfold Mem.ptr2int in CMPI. des_ifs. ss. inv Heq. eauto.
  - exfalso. unfold to_int_val in CMPI; ss. unfold Mem.ptr2int in CMPI. des_ifs.
Qed.

Lemma psubl_always_captured2 i b ofs n
    (SUCCESS: psubl_join (Vptr b ofs) (Vlong i) = Vlong n) :
  exists caddr, (Mem.mem_concrete m) ! b = Some caddr.
Proof.
  unfold psubl_join in *. unfold val_join in *. des_ifs.
  - unfold Val.psubl in SUCCESS. des_ifs. unfold to_int_val in Heq0. ss. des_ifs_safe.
    unfold Mem.ptr2int in Heq3. des_ifs_safe. eauto.
  - unfold Val.psubl in Heq. des_ifs. unfold to_ptr_val in *. ss. des_ifs_safe.
    ss. inv Heq2. eapply Mem.denormalize_info in Heq4. des; eauto.
  - unfold Val.psubl in Heq0. des_ifs. unfold to_int_val in Heq2. ss. des_ifs.
    unfold Mem.ptr2int in Heq0. des_ifs. eauto.
Qed.

Lemma cmplu_always_captured2 c i b ofs bi
    (NOTEQ: c <> Ceq /\ c <> Cne)
    (NOTNULL: Int64.eq i Int64.zero = false)
    (SUCCESS: cmplu_join c (Vptr b ofs) (Vlong i) = Some bi) :
  exists caddr, (Mem.mem_concrete m) ! b = Some caddr.
Proof.
  unfold cmplu_join in *. unfold bool_optjoin in *.
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_int_val m (Vptr b ofs)) (to_int_val m (Vlong i))) eqn:CMPI;
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_ptr_val m (Vptr b ofs)) (to_ptr_val m (Vlong i))) eqn:CMPP; ss.
  - clear CMPP. unfold Val.cmplu_bool in CMPI. des_ifs.
    { unfold to_int_val in Heq. ss. des_ifs.
      unfold Mem.ptr2int in Heq1. des_ifs. eauto. }
    { unfold to_int_val in Heq. ss. des_ifs. }
  - clear CMPP. unfold Val.cmplu_bool in CMPI. des_ifs.
    { unfold to_int_val in Heq. ss. des_ifs.
      unfold Mem.ptr2int in Heq1. des_ifs. eauto. }
    { unfold to_int_val in Heq. ss. des_ifs. }
  - clear CMPI. des_ifs.
    { destruct c; ss; des; clarify. }
    { unfold to_ptr_val, Mem.to_ptr in *. des_ifs. ss. clarify.
      eapply Mem.denormalize_info in Heq3. des. eauto. }
    { destruct c; ss; des; clarify. }
Qed.

Lemma cmplu_always_captured2' c i b ofs caddr
    (CAP: (Mem.mem_concrete m) ! b = Some caddr) :
  <<SUCCESS: cmplu_join c (Vptr b ofs) (Vlong i) = Some (Int64.cmpu c (Int64.repr (caddr + Ptrofs.unsigned ofs)) i)>>.
Proof.
  unfold cmplu_join.
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_ptr_val m (Vptr b ofs)) (to_ptr_val m (Vlong i))) eqn: CMPP;
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_int_val m (Vptr b ofs)) (to_int_val m (Vlong i))) eqn: CMPI.
  - rewrite bool_optjoin_angelic_vi; eauto.
    { ss. unfold to_int_val in CMPI; ss. unfold Mem.ptr2int in CMPI. des_ifs. }
    left. f_equal. eapply cmplu_no_angelic; eauto.
  - exfalso. unfold to_int_val in CMPI; ss. unfold Mem.ptr2int in CMPI. des_ifs.
  - rewrite bool_optjoin_angelic_vi; eauto.
    unfold to_int_val in CMPI; ss. unfold Mem.ptr2int in CMPI. des_ifs.
  - exfalso. unfold to_int_val in CMPI; ss. unfold Mem.ptr2int in CMPI. des_ifs.
Qed.

Lemma psubl_always_captured1' b caddr i ofs
    (CAP: (Mem.mem_concrete m) ! b = Some caddr) :
  <<SUCCESS: psubl_join (Vlong i) (Vptr b ofs) = Vlong (Int64.sub i (Int64.repr (caddr + Ptrofs.unsigned ofs)))>>.
Proof.
  unfold psubl_join. unfold val_join.
  assert (Val.psubl (to_int_val m (Vlong i)) (to_int_val m (Vptr b ofs)) 
          = Vlong (Int64.sub i (Int64.repr (caddr + Ptrofs.unsigned ofs)))).
  { unfold to_int_val; ss. unfold Mem.ptr2int. rewrite CAP. des_ifs. }
  exploit psubl_wrapper_no_angelic; eauto. i. des; des_ifs.
  rewrite Int64.eq_true in Heq1. clarify.
Qed.

Lemma psubl_always_captured2' b caddr i ofs
    (CAP: (Mem.mem_concrete m) ! b = Some caddr) :
  <<SUCCESS: psubl_join (Vptr b ofs) (Vlong i) = Vlong (Int64.sub (Int64.repr (caddr + Ptrofs.unsigned ofs)) i)>>.
Proof.
  unfold psubl_join. unfold val_join.
  assert (Val.psubl (to_int_val m (Vptr b ofs)) (to_int_val m (Vlong i))
          = Vlong (Int64.sub (Int64.repr (caddr + Ptrofs.unsigned ofs)) i)).
  { unfold to_int_val; ss. unfold Mem.ptr2int. rewrite CAP. ss. }
  exploit psubl_wrapper_no_angelic; eauto. i. des; des_ifs.
  rewrite Int64.eq_true in Heq1. clarify.
Qed.

Lemma psub_always_captured1' b caddr i ofs
    (SF: Archi.ptr64 = false)
    (CAP: (Mem.mem_concrete m) ! b = Some caddr) :
  <<SUCCESS: psub_join (Vint i) (Vptr b ofs) = Vint (Int.sub i (Int.repr (caddr + Ptrofs.unsigned ofs)))>>.
Proof.
  unfold psub_join, val_join.
  assert (Val.psub (to_int_val m (Vint i)) (to_int_val m (Vptr b ofs)) 
          = Vint (Int.sub i (Int.repr (caddr + Ptrofs.unsigned ofs)))).
  { unfold to_int_val; simpl. unfold Mem.ptr2int. rewrite SF, CAP. des_ifs. }
  eapply psub_wrapper_no_angelic in H; [|eauto]. i.
  unfold to_int_val, Mem.to_int in *; simpl in *. unfold Mem.ptr2int in *. rewrite SF in *.
  clear SF. des; des_ifs. ss. inv Heq0. ss.
Qed.

Lemma psub_always_captured2' b caddr i ofs
  (SF: Archi.ptr64 = false)
  (CAP: (Mem.mem_concrete m) ! b = Some caddr) :
  <<SUCCESS: psub_join (Vptr b ofs) (Vint i) = Vint (Int.sub (Int.repr (caddr + Ptrofs.unsigned ofs)) i)>>.
Proof.
  unfold psub_join, val_join.
  assert (Val.psub (to_int_val m (Vptr b ofs)) (to_int_val m (Vint i))
          = Vint (Int.sub (Int.repr (caddr + Ptrofs.unsigned ofs)) i)).
  { unfold to_int_val; simpl. unfold Mem.ptr2int. rewrite SF, CAP. des_ifs. }
  eapply psub_wrapper_no_angelic in H; [|eauto]. i.
  unfold to_int_val, Mem.to_int in *; simpl in *. unfold Mem.ptr2int in *.
  rewrite CAP, SF in *. simpl in *. rewrite SF.
  simpl in *. clear SF. des; rewrite H.
  - reflexivity.
  - inv H.
  - rewrite <- H. rewrite Int.eq_true. reflexivity.
Qed.

Lemma psubl_always_captured1_undef b i ofs
    (CAP: (Mem.mem_concrete m) ! b = None) :
  <<FAIL: psubl_join (Vlong i) (Vptr b ofs) = Vundef>>.
Proof.
  unfold psubl_join, to_int_val. ss. unfold Mem.ptr2int. rewrite CAP. ss.
  destruct (to_ptr_val m (Vlong i)) eqn:TOPTR; ss.
  unfold to_ptr_val in TOPTR. ss. des_ifs. ss. clarify.
  eapply Mem.denormalize_info in Heq2. des. clarify.
Qed.

Lemma psubl_always_captured2_undef b i ofs
    (CAP: (Mem.mem_concrete m) ! b = None) :
  <<FAIL: psubl_join (Vptr b ofs) (Vlong i) = Vundef>>.
Proof.
  unfold psubl_join, to_int_val. ss. unfold Mem.ptr2int. rewrite CAP. ss.
  destruct (to_ptr_val m (Vlong i)) eqn:TOPTR; ss.
  unfold to_ptr_val in TOPTR. ss. des_ifs. ss. clarify.
  eapply Mem.denormalize_info in Heq2. des. clarify.
Qed.

Lemma psub_always_captured1_undef b i ofs
    (SF: Archi.ptr64 = false)
    (CAP: (Mem.mem_concrete m) ! b = None) :
  <<FAIL: psub_join (Vint i) (Vptr b ofs) = Vundef>>.
Proof.
  unfold psub_join, to_int_val. simpl. unfold Mem.ptr2int. rewrite SF, CAP. simpl.
  destruct (to_ptr_val m (Vint i)) eqn:TOPTR;
  unfold to_ptr_val in *; simpl in *; try rewrite SF in *; clear SF; auto.
  simpl in *. des_ifs. eapply Mem.denormalize_info in Heq0. des. ss; clarify.
Qed.

Lemma psub_always_captured2_undef b i ofs
    (SF: Archi.ptr64 = false)
    (CAP: (Mem.mem_concrete m) ! b = None) :
  <<FAIL: psub_join (Vptr b ofs) (Vint i) = Vundef>>.
Proof.
  unfold psub_join, to_int_val. simpl. unfold Mem.ptr2int. rewrite SF, CAP. simpl.
  destruct (to_ptr_val m (Vint i)) eqn:TOPTR;
  unfold to_ptr_val in *; simpl in *; try rewrite SF in *; clear SF; auto.
  simpl in *. des_ifs. eapply Mem.denormalize_info in Heq0. des. ss; clarify.
Qed.

Lemma psubl_join_addl_l v1 v2 i:
  psubl_join (Val.addl v1 (Vlong i)) v2 = Val.addl (psubl_join v1 v2) (Vlong i).
Proof.
  destruct v1; simpl; eauto.
  - rename i0 into n1. destruct v2; try (by (unfold psubl_join, to_ptr_val, to_int_val; ss; des_ifs)).
    (* long long *)
    + rename i0 into n2. unfold psubl_join.
      assert (Val.psubl (to_int_val m (Vlong (Int64.add n1 i))) (to_int_val m (Vlong n2))
              = Vlong (Int64.sub (Int64.add n1 i) n2)) by ss.
      assert (Val.psubl (to_int_val m (Vlong n1)) (to_int_val m (Vlong n2)) = Vlong (Int64.sub n1 n2)) by ss.
      exploit psubl_wrapper_no_angelic; try eapply H; eauto.
      exploit psubl_wrapper_no_angelic; try eapply H0; eauto. i.
      exploit val_join_angelic_vi; try eapply H1; try (by ss). i.
      exploit val_join_angelic_vi; try eapply H2; try (by ss). i. clear H1 H2. des.
      unfold to_int_val. ss. destruct Archi.ptr64 eqn:SF; [|clarify].
      rewrite H3, H4. ss. f_equal. rewrite Int64.sub_add_l. eauto.
    (* long ptr *)
    + rename b into b2. rename i0 into ofs2.
      destruct ((Mem.mem_concrete m) ! b2) eqn:CONC.
      { erewrite psubl_always_captured1'; eauto. erewrite psubl_always_captured1'; eauto.
        ss. f_equal. rewrite Int64.sub_add_l. eauto. }
      rewrite psubl_always_captured1_undef; eauto. rewrite psubl_always_captured1_undef; eauto.
  - rename b into b1. rename i0 into ofs1. destruct Archi.ptr64 eqn:SF; [|clarify].
    destruct v2; try (by (unfold psubl_join, to_ptr_val, to_int_val; ss; des_ifs)).
    (* ptr long *)
    + destruct ((Mem.mem_concrete m) ! b1) eqn:CONC.
      { erewrite psubl_always_captured2'; eauto. erewrite psubl_always_captured2'; eauto.
        ss. f_equal. rewrite <- Int64.sub_add_l.
        replace (Int64.repr (z + Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.of_int64 i))))
          with (Int64.add (Int64.repr (z + Ptrofs.unsigned ofs1)) i); eauto.
        { unfold Int64.add. eapply Int64.same_if_eq. unfold Ptrofs.add. unfold Ptrofs.of_int64.
          do 2 rewrite Ptrofs.unsigned_repr_eq. unfold Int64.eq. des_ifs. exfalso. eapply n.
          do 3 rewrite Int64.unsigned_repr_eq. rewrite Ptrofs.modulus_eq64; eauto.
          rewrite (Zplus_mod_idemp_r (Int64.unsigned i) (Ptrofs.unsigned ofs1)). rewrite Zplus_mod_idemp_l.
          rewrite Zplus_mod_idemp_r. rewrite Z.add_assoc. auto. } }
      rewrite psubl_always_captured2_undef; eauto. rewrite psubl_always_captured2_undef; eauto.
    (* ptr ptr *)
    + rename b into b2. rename i0 into ofs2. unfold psubl_join.
      destruct (eq_block b1 b2); subst.
      * assert (Val.psubl (to_ptr_val m (Vptr b2 (Ptrofs.add ofs1 (Ptrofs.of_int64 i)))) (to_ptr_val m (Vptr b2 ofs2))
                =  Vlong (Ptrofs.to_int64 (Ptrofs.sub (Ptrofs.add ofs1 (Ptrofs.of_int64 i)) ofs2))) by (ss; des_ifs).
        assert (Val.psubl (to_ptr_val m (Vptr b2 ofs1)) (to_ptr_val m (Vptr b2 ofs2))
                = Vlong (Ptrofs.to_int64 (Ptrofs.sub ofs1 ofs2))) by (ss; des_ifs).
        exploit psubl_wrapper_no_angelic; try eapply H; eauto.
        exploit psubl_wrapper_no_angelic; try eapply H0; eauto. i.
        exploit val_join_angelic_vp; try eapply H1; try (by ss). i.
        exploit val_join_angelic_vp; try eapply H2; try (by ss). i. clear H1 H2. des.
        simpl. rewrite SF. destruct (eq_block b2 b2); [|clarify]. des_ifs.
        rewrite H3, H4. simpl. f_equal.
        unfold Ptrofs.to_int64, Ptrofs.sub, Int64.add, Ptrofs.add, Ptrofs.to_int64, Ptrofs.of_int64.
        repeat rewrite Ptrofs.unsigned_repr_eq. eapply Int64.same_if_eq. unfold Int64.eq. des_ifs. exfalso. eapply n.
        repeat rewrite Int64.unsigned_repr_eq. repeat (rewrite Ptrofs.modulus_eq64; eauto).
        rewrite Zplus_mod_idemp_r. rewrite Zminus_mod_idemp_l. do 2 rewrite Zplus_mod_idemp_l.
        rewrite Z.mod_mod. 2:{ specialize Int64.modulus_pos. lia. } f_equal. lia.
      * simpl. rewrite SF. simpl. des_ifs. simpl. unfold to_int_val; simpl. unfold Mem.ptr2int.
        destruct ((Mem.mem_concrete m) ! b1) eqn:CONC1;
          destruct ((Mem.mem_concrete m) ! b2) eqn:CONC2; try rewrite SF; simpl; eauto.
        { rewrite SF. unfold Val.addl. f_equal. rewrite <- Int64.sub_add_l.
          unfold Int64.add, Int64.sub, Ptrofs.add, Ptrofs.of_int64.
          eapply Int64.same_if_eq. unfold Int64.eq. des_ifs. exfalso. eapply n1.
          repeat rewrite Ptrofs.unsigned_repr_eq. repeat rewrite Int64.unsigned_repr_eq.
          rewrite (Zplus_mod_idemp_r (Int64.unsigned i) (Ptrofs.unsigned ofs1)).
          repeat rewrite Zplus_mod_idemp_r. repeat rewrite Zplus_mod_idemp_l.
          repeat rewrite Zminus_mod_idemp_r. repeat rewrite Zminus_mod_idemp_l. f_equal. lia. }
Qed.

Definition psubl_join_common (arg1 arg2: val) :=
  match arg1, arg2 with
  | Vptr _ _, Vptr _ _ | Vlong _, Vlong _ => (Val.psubl arg1 arg2)
  | Vptr _ _, Vlong _ | Vlong _, Vptr _ _ => (psubl_join arg1 arg2)
  | _, _ => Vundef
  end.

Definition psub_join_common (arg1 arg2: val) :=
  match arg1, arg2 with
  | Vptr _ _, Vptr _ _ | Vint _, Vint _ => (Val.psub arg1 arg2)
  | Vptr _ _, Vint _ | Vint _, Vptr _ _ => (psub_join arg1 arg2)
  | _, _ => Vundef
  end.

(* Definition psubl_join_common_src (arg1 arg2: val) := *)
(*   match arg1, arg2 with *)
(*   | Vptr _ _, Vptr _ _ | Vlong _, Vlong _ => (Val.psubl arg1 arg2) *)
(*   | Vptr _ _, Vlong n | Vlong n, Vptr _ _ => if Int64.eq n Int64.zero then Vundef else (psubl_join arg1 arg2) *)
(*   | _, _ => Vundef *)
(*   end. *)

(* Definition psub_join_common_src (arg1 arg2: val) := *)
(*   match arg1, arg2 with *)
(*   | Vptr _ _, Vptr _ _ | Vint _, Vint _ => (Val.psub arg1 arg2) *)
(*   | Vptr _ _, Vint n | Vint n, Vptr _ _ => if Int.eq n Int.zero then Vundef else (psub_join arg1 arg2) *)
(*   | _, _ => Vundef *)
(*   end. *)

(* Lemma psubl_join_common_refine v1 v2: Val.lessdef (psubl_join_common_src v1 v2) (psubl_join_common v1 v2). *)
(* Proof. unfold psubl_join_common, psubl_join_common_src. des_ifs. Qed. *)

(* Lemma psub_join_common_refine v1 v2: Val.lessdef (psub_join_common_src v1 v2) (psub_join_common v1 v2). *)
(* Proof. unfold psub_join_common, psub_join_common_src. des_ifs. Qed. *)

Lemma psubl_join_common_addl_l v1 v2 i:
  psubl_join_common (Val.addl v1 (Vlong i)) v2 = Val.addl (psubl_join_common v1 v2) (Vlong i).
Proof.
  destruct v1; destruct v2; ss; des_ifs.
  - ss. rewrite Int64.sub_add_l. eauto.
  - erewrite <- psubl_join_addl_l. ss.
  - ss. erewrite <- psubl_join_addl_l. ss.
  - ss. des_ifs. f_equal. unfold Ptrofs.sub, Ptrofs.to_int64, Int64.add, Ptrofs.add, Ptrofs.of_int64.
    eapply Int64.same_if_eq. unfold Int64.eq. des_ifs. exfalso. eapply n.
    repeat rewrite Ptrofs.unsigned_repr_eq. repeat rewrite Int64.unsigned_repr_eq.
    repeat rewrite Zplus_mod_idemp_r. repeat rewrite Zplus_mod_idemp_l.
    repeat rewrite Zminus_mod_idemp_l. rewrite Zmod_mod. f_equal. lia.
  - ss. des_ifs.
Qed.
 
Lemma psubl_join_common_addl_r v1 v2 i:
  psubl_join_common v1 (Val.addl v2 (Vlong i)) = Val.addl (psubl_join_common v1 v2) (Vlong (Int64.neg i)).
Proof.
  destruct v1; destruct v2; ss; des_ifs.
  (* int int *)
  - simpl. rewrite <- Int64.sub_add_r. rewrite Int64.add_commut. eauto.
  (* int ptr *)
  - rename b0 into b2. rename i1 into ofs2.
    destruct ((Mem.mem_concrete m) ! b2) eqn:CONC.
    { erewrite psubl_always_captured1'; eauto. erewrite psubl_always_captured1'; eauto.
      ss. f_equal. rewrite <- Int64.sub_add_r. f_equal.
      unfold Ptrofs.add, Ptrofs.of_int64, Int64.add.
      eapply Int64.same_if_eq. unfold Int64.eq. des_ifs. exfalso. eapply n.
      repeat rewrite Ptrofs.unsigned_repr_eq. repeat rewrite Int64.unsigned_repr_eq.
      rewrite (Zplus_mod_idemp_r (Int64.unsigned i)). repeat rewrite Zplus_mod_idemp_r. f_equal. lia. }
    rewrite psubl_always_captured1_undef; eauto. rewrite psubl_always_captured1_undef; eauto.
  (* ptr int *)
  - rename b into b1. rename i0 into ofs1.
    destruct ((Mem.mem_concrete m) ! b1) eqn:CONC.
    { erewrite psubl_always_captured2'; eauto. erewrite psubl_always_captured2'; eauto.
      ss. f_equal. rewrite <- Int64.sub_add_r. rewrite Int64.add_commut. eauto. }
    rewrite psubl_always_captured2_undef; eauto. rewrite psubl_always_captured2_undef; eauto.
  - ss. f_equal. unfold Ptrofs.to_int64, Ptrofs.sub, Ptrofs.add, Ptrofs.of_int64, Int64.add, Int64.neg.
    eapply Int64.same_if_eq. unfold Int64.eq. des_ifs. exfalso. eapply n.
    repeat rewrite Ptrofs.unsigned_repr_eq. repeat rewrite Int64.unsigned_repr_eq.
    rewrite (Zplus_mod_idemp_r (Int64.unsigned i)). repeat rewrite Zminus_mod_idemp_r.
    repeat rewrite Zmod_mod. rewrite Zplus_mod_idemp_r. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma psub_join_common_addl_l v1 v2 i:
  psub_join_common (Val.add v1 (Vint i)) v2 = Val.add (psub_join_common v1 v2) (Vint i).
Proof.
  destruct Archi.ptr64 eqn:SF.
  { unfold psub_join_common. unfold psub_join, Val.psub. rewrite SF. des_ifs. }
  destruct v1; destruct v2; simpl in *; try rewrite SF; auto.
  - simpl. rewrite Int.sub_add_l. eauto.
  (* int ptr *)
  - rename b into b2. rename i1 into ofs2.
    destruct ((Mem.mem_concrete m) ! b2) eqn:CONC.
    { erewrite psub_always_captured1'; eauto. erewrite psub_always_captured1'; eauto.
      simpl. f_equal. rewrite <- Int.sub_add_l. reflexivity. }
    rewrite psub_always_captured1_undef; eauto. rewrite psub_always_captured1_undef; eauto.
  (* ptr int *)
  - simpl. rename b into b1. rename i0 into ofs1.
    destruct ((Mem.mem_concrete m) ! b1) eqn:CONC.
    { erewrite psub_always_captured2'; eauto. erewrite psub_always_captured2'; eauto.
      simpl. f_equal. rewrite <- Int.sub_add_l. f_equal. ss. }
    rewrite psub_always_captured2_undef; eauto. rewrite psub_always_captured2_undef; eauto.
  - simpl. rewrite SF. destruct (eq_block b b0); [|simpl; auto]. ss.
Qed.
 
Lemma psub_join_common_addl_r v1 v2 i:
  psub_join_common v1 (Val.add v2 (Vint i)) = Val.add (psub_join_common v1 v2) (Vint (Int.neg i)).
Proof.
  destruct Archi.ptr64 eqn:SF.
  { unfold psub_join_common. unfold psub_join, Val.psub. rewrite SF. des_ifs. }
  destruct v1; destruct v2; simpl in *; try rewrite SF; auto.
  - simpl. rewrite Int.add_commut. rewrite Int.sub_add_r. reflexivity.
  (* int ptr *)
  - rename b into b2. rename i1 into ofs2.
    destruct ((Mem.mem_concrete m) ! b2) eqn:CONC.
    { erewrite psub_always_captured1'; eauto. erewrite psub_always_captured1'; eauto.
      simpl. f_equal. rewrite <- Int.sub_add_r. ss. }
    rewrite psub_always_captured1_undef; eauto. rewrite psub_always_captured1_undef; eauto.
  (* ptr int *)
  - simpl. rename b into b1. rename i0 into ofs1.
    destruct ((Mem.mem_concrete m) ! b1) eqn:CONC.
    { erewrite psub_always_captured2'; eauto. erewrite psub_always_captured2'; eauto.
      simpl. f_equal. rewrite <- Int.sub_add_r. rewrite Int.add_commut. reflexivity. }
    rewrite psub_always_captured2_undef; eauto. rewrite psub_always_captured2_undef; eauto.
  - simpl. destruct (eq_block b b0); [|simpl; auto]. ss.
Qed.

End PTRBINJOIN.

Section GENREL.

Variable f: meminj.
Variable m1: mem.
Variable m2: mem.

Hypothesis mi_inj_perm: forall b1 b2 delta ofs k p,
    f b1 = Some (b2, delta) ->
    Mem.perm m1 b1 ofs k p -> Mem.perm m2 b2 (ofs + delta) k p.

Hypothesis valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_pointer_no_overflow:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.

Hypothesis valid_different_pointers_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m1 b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).

Hypothesis src_concrete_private: forall b, f b = None -> (Mem.mem_concrete m1) ! b = None.

Hypothesis mappedblocks: forall b b' delta, Mem.valid_block m1 b -> f b = Some (b', delta) -> Mem.valid_block m2 b'.

Hypothesis src_concrete_public: forall b1 b2 addr delta,
    f b1 = Some (b2, delta) ->
    (Mem.mem_concrete m1) ! b1 = Some addr ->
    (Mem.mem_concrete m2) ! b2 = Some (addr - delta).

Hypothesis representable: forall b b' delta ofs,
    f b = Some (b', delta) ->
    Mem.perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/
    Mem.perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
    delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned.

Lemma psubl_join_inj
    v1 v1' v2 v2' v
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (PSUB: psubl_join m1 v1 v2 = v) :
  exists v', <<PSUB: psubl_join m2 v1' v2' = v'>> /\ <<VINJ: Val.inject f v v'>>.
Proof.
  unfold psubl_join in *.
  exploit to_int_val_inject'; try eapply VINJ1; eauto. i. exploit to_int_val_inject'; try eapply VINJ2; eauto. i.
  exploit to_ptr_val_inject'; try eapply VINJ1; eauto. i. exploit to_ptr_val_inject'; try eapply VINJ2; eauto. i.
  exploit (psubl_wrapper_no_angelic m1 v1 v2); eauto. i.
  exploit (Val.psubl_inject f (to_ptr_val m1 v1) (to_ptr_val m2 v1') (to_ptr_val m1 v2) (to_ptr_val m2 v2')); eauto. i.
  exploit (Val.psubl_inject f (to_int_val m1 v1) (to_int_val m2 v1') (to_int_val m1 v2) (to_int_val m2 v2')); eauto. i.
  r in H4. r in H5. des.
  - rewrite H3 in *. destruct (classic ((Val.psubl (to_int_val m1 v1) (to_int_val m1 v2)) = Vundef)).
    { rewrite H6 in *. ss. inv PSUB. esplits; eauto. }
    subst. rewrite val_join_angelic_vi; eauto.
    { eapply psubl_is_only_int. }
    { eapply psubl_wrapper_no_angelic; eauto. }
    { ii. rewrite H7 in *. inv H5; clarify. rewrite <- H9 in *. clarify. }
  - rewrite H3 in *. destruct (classic ((Val.psubl (to_ptr_val m1 v1) (to_ptr_val m1 v2)) = Vundef)).
    { rewrite H6 in *. ss. inv PSUB. esplits; eauto. }
    subst. rewrite (val_join_angelic_vp _ Vundef); eauto.
    2:{ eapply psubl_is_only_int. }
    rewrite val_join_angelic_vp; eauto.
    { eapply psubl_is_only_int. }
    { eapply psubl_wrapper_no_angelic; eauto. }
    { ii. rewrite H7 in *. inv H4; eauto. }
  - destruct (classic ((Val.psubl (to_int_val m1 v1) (to_int_val m1 v2)) = Vundef)).
    { rewrite H3, H6 in *. ss. subst. esplits; eauto. }
    rewrite <- H3 in PSUB. rewrite val_join_same_val in PSUB.
    2:{ eapply psubl_is_only_int. }
    subst. rewrite val_join_angelic_vi; eauto.
    { eapply psubl_is_only_int. }
    { eapply psubl_wrapper_no_angelic; eauto. }
    { ii. rewrite H7 in *. inv H5; eauto. }
Qed.

Lemma psub_join_inj
    v1 v1' v2 v2' v
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (PSUB: psub_join m1 v1 v2 = v) :
  exists v', <<PSUB: psub_join m2 v1' v2' = v'>> /\ <<VINJ: Val.inject f v v'>>.
Proof.
  unfold psub_join in *.
  exploit to_int_val_inject'; try eapply VINJ1; eauto. i. exploit to_int_val_inject'; try eapply VINJ2; eauto. i.
  exploit to_ptr_val_inject'; try eapply VINJ1; eauto. i. exploit to_ptr_val_inject'; try eapply VINJ2; eauto. i.
  exploit (psub_wrapper_no_angelic m1 v1 v2); eauto. i.
  exploit (Val.psub_inject f (to_ptr_val m1 v1) (to_ptr_val m2 v1') (to_ptr_val m1 v2) (to_ptr_val m2 v2')); eauto. i.
  exploit (Val.psub_inject f (to_int_val m1 v1) (to_int_val m2 v1') (to_int_val m1 v2) (to_int_val m2 v2')); eauto. i.
  r in H4. r in H5. des.
  - rewrite H3 in *. destruct (classic ((Val.psub (to_int_val m1 v1) (to_int_val m1 v2)) = Vundef)).
    { rewrite H6 in *. ss. inv PSUB. esplits; eauto. }
    subst. rewrite val_join_angelic_vi; eauto.
    { eapply psub_is_only_int. }
    { eapply psub_wrapper_no_angelic; eauto. }
    { ii. rewrite H7 in *. inv H5; clarify. rewrite <- H9 in *. clarify. }
  - rewrite H3 in *. destruct (classic ((Val.psub (to_ptr_val m1 v1) (to_ptr_val m1 v2)) = Vundef)).
    { rewrite H6 in *. ss. inv PSUB. esplits; eauto. }
    subst. rewrite (val_join_angelic_vp _ Vundef); eauto.
    2:{ eapply psub_is_only_int. }
    rewrite val_join_angelic_vp; eauto.
    { eapply psub_is_only_int. }
    { eapply psub_wrapper_no_angelic; eauto. }
    { ii. rewrite H7 in *. inv H4; eauto. }
  - destruct (classic ((Val.psub (to_int_val m1 v1) (to_int_val m1 v2)) = Vundef)).
    { rewrite H3, H6 in *. ss. subst. esplits; eauto. }
    rewrite <- H3 in PSUB. rewrite val_join_same_val in PSUB.
    2:{ eapply psub_is_only_int. }
    subst. rewrite val_join_angelic_vi; eauto.
    { eapply psub_is_only_int. }
    { eapply psub_wrapper_no_angelic; eauto. }
    { ii. rewrite H7 in *. inv H5; eauto. }
Qed.

Lemma psubl_join_common_inj
    v1 v1' v2 v2' v
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (PSUB: psubl_join_common m1 v1 v2 = v) :
  exists v', <<PSUB: psubl_join_common m2 v1' v2' = v'>> /\ <<VINJ: Val.inject f v v'>>.
Proof.
  destruct Archi.ptr64 eqn:SF; cycle 1.
  { esplits; eauto. unfold psubl_join_common, psubl_join, Val.psubl in PSUB.
    rewrite SF in *. clear SF. inv VINJ1; inv VINJ2; simpl in *; esplits; eauto; des_ifs. }
  destruct v1, v2; simpl in *; try rewrite SF in *; try by (clear SF; subst v; esplits; eauto).
- inv VINJ1; inv VINJ2; simpl. rewrite SF. clear SF. esplits; eauto.
- exploit psubl_join_inj; try eapply PSUB; eauto. i. des; subst.
  inv VINJ1; inv VINJ2; simpl. esplits; eauto.
- exploit psubl_join_inj; try eapply PSUB; eauto. i. des; subst.
  inv VINJ1; inv VINJ2; simpl. esplits; eauto.
- exploit Val.psubl_inject. eapply VINJ1. eapply VINJ2.
  inv VINJ1; inv VINJ2. simpl in *. rewrite SF. esplits; eauto.
Qed.

Lemma psub_join_common_inj
    v1 v1' v2 v2' v
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (PSUB: psub_join_common m1 v1 v2 = v) :
  exists v', <<PSUB: psub_join_common m2 v1' v2' = v'>> /\ <<VINJ: Val.inject f v v'>>.
Proof.
  destruct Archi.ptr64 eqn:SF.
  { esplits; eauto. unfold psub_join_common, psub_join, Val.psub in PSUB.
    rewrite SF in *. clear SF. inv VINJ1; inv VINJ2; simpl in *; esplits; eauto; des_ifs. }
  destruct v1, v2; simpl in *; try rewrite SF in *; try by (clear SF; subst v; esplits; eauto).
- inv VINJ1; inv VINJ2; simpl. rewrite SF. clear SF. esplits; eauto.
- exploit psub_join_inj; try eapply PSUB; eauto. i. des; subst.
  inv VINJ1; inv VINJ2; simpl. esplits; eauto.
- exploit psub_join_inj; try eapply PSUB; eauto. i. des; subst.
  inv VINJ1; inv VINJ2; simpl. esplits; eauto.
- exploit Val.psub_inject. eapply VINJ1. eapply VINJ2.
  inv VINJ1; inv VINJ2. simpl in *. rewrite SF. esplits; eauto.
Qed.

Lemma cmplu_join_inj
    c v1 v2 v1' v2' b
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (CMP: cmplu_join m1 c v1 v2 = Some b) :
  <<CMP: cmplu_join m2 c v1' v2' = Some b>>.
Proof.
  unfold cmplu_join in *.
  exploit to_int_val_inject'; try eapply VINJ1; eauto. i. exploit to_int_val_inject'; try eapply VINJ2; eauto. i.
  exploit to_ptr_val_inject'; try eapply VINJ1; eauto. i. exploit to_ptr_val_inject'; try eapply VINJ2; eauto. i.
  destruct (Val.cmplu_bool (Mem.valid_pointer m1) c (to_ptr_val m1 v1) (to_ptr_val m1 v2)) eqn:PCMP.
  - destruct (Val.cmplu_bool (Mem.valid_pointer m1) c (to_int_val m1 v1) (to_int_val m1 v2)) eqn:ICMP.
    + exploit cmplu_no_angelic; eauto. i. des; subst.
      erewrite Val.cmplu_bool_inject; try eapply PCMP; eauto. erewrite Val.cmplu_bool_inject; try eapply ICMP; eauto.
    + exploit Val.cmplu_bool_inject; try eapply PCMP; eauto. i.
      destruct (Val.cmplu_bool (Mem.valid_pointer m2) c (to_int_val m2 v1') (to_int_val m2 v2')) eqn:ICMP'.
      { exploit cmplu_no_angelic; eauto. i. des; subst. rewrite H3. rewrite bool_optjoin_same_bool. ss. }
      rewrite H3. ss.
  - destruct (Val.cmplu_bool (Mem.valid_pointer m1) c (to_int_val m1 v1) (to_int_val m1 v2)) eqn:ICMP; [|ss].
    exploit Val.cmplu_bool_inject; try eapply ICMP; eauto. i. rewrite H3.
    destruct (Val.cmplu_bool (Mem.valid_pointer m2) c (to_ptr_val m2 v1') (to_ptr_val m2 v2')) eqn:PCMP'; [|ss].
    exploit cmplu_no_angelic; eauto. i. des; subst. simpl in CMP. inv CMP. eapply bool_optjoin_same_bool.
Qed.

Lemma cmpu_join_inj c v1 v2 v1' v2' b
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (CMP: cmpu_join m1 c v1 v2 = Some b) :
  <<CMP: cmpu_join m2 c v1' v2' = Some b>>.
Proof.
  unfold cmpu_join in *.
  exploit to_int_val_inject'; try eapply VINJ1; eauto. i. exploit to_int_val_inject'; try eapply VINJ2; eauto. i.
  exploit to_ptr_val_inject'; try eapply VINJ1; eauto. i. exploit to_ptr_val_inject'; try eapply VINJ2; eauto. i.
  destruct (Val.cmpu_bool (Mem.valid_pointer m1) c (to_ptr_val m1 v1) (to_ptr_val m1 v2)) eqn:PCMP.
  - destruct (Val.cmpu_bool (Mem.valid_pointer m1) c (to_int_val m1 v1) (to_int_val m1 v2)) eqn:ICMP.
    + exploit cmpu_no_angelic; eauto. i. des; subst.
      erewrite Val.cmpu_bool_inject; try eapply PCMP; eauto. erewrite Val.cmpu_bool_inject; try eapply ICMP; eauto.
    + exploit Val.cmpu_bool_inject; try eapply PCMP; eauto. i.
      destruct (Val.cmpu_bool (Mem.valid_pointer m2) c (to_int_val m2 v1') (to_int_val m2 v2')) eqn:ICMP'.
      { exploit cmpu_no_angelic; eauto. i. des; subst. rewrite H3. rewrite bool_optjoin_same_bool. ss. }
      rewrite H3. ss.
  - destruct (Val.cmpu_bool (Mem.valid_pointer m1) c (to_int_val m1 v1) (to_int_val m1 v2)) eqn:ICMP; [|ss].
    exploit Val.cmpu_bool_inject; try eapply ICMP; eauto. i. rewrite H3.
    destruct (Val.cmpu_bool (Mem.valid_pointer m2) c (to_ptr_val m2 v1') (to_ptr_val m2 v2')) eqn:PCMP'; [|ss].
    exploit cmpu_no_angelic; eauto. i. des; subst. simpl in CMP. inv CMP. eapply bool_optjoin_same_bool.
Qed.

Lemma cmplu_join_common_inj
    c v1 v2 v1' v2' b
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (CMP: cmplu_join_common m1 c v1 v2 = Some b) :
  <<CMP: cmplu_join_common m2 c v1' v2' = Some b>>.
Proof.
  unfold cmplu_join_common in *. inv VINJ1; inv VINJ2; try by inv CMP.
  - des_ifs.
    + eapply Val.cmplu_bool_inject; try eapply CMP; eauto.
    + eapply cmplu_join_inj; try eapply CMP; eauto.
  - des_ifs.
    + eapply Val.cmplu_bool_inject; try eapply CMP; eauto.
    + eapply cmplu_join_inj; try eapply CMP; eauto.
  - eapply Val.cmplu_bool_inject; try eapply CMP; eauto.
Qed.

Lemma cmpu_join_common_inj
    c v1 v2 v1' v2' b
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (CMP: cmpu_join_common m1 c v1 v2 = Some b) :
  <<CMP: cmpu_join_common m2 c v1' v2' = Some b>>.
Proof.
  unfold cmpu_join_common in *. inv VINJ1; inv VINJ2; try by inv CMP.
  - destruct (Int.eq i Int.zero) eqn:NULL.
    + eapply Val.cmpu_bool_inject; try eapply CMP; eauto.
    + eapply cmpu_join_inj; try eapply CMP; eauto.
  - destruct (Int.eq i Int.zero) eqn:NULL.
    + eapply Val.cmpu_bool_inject; try eapply CMP; eauto.
    + eapply cmpu_join_inj; try eapply CMP; eauto.
Qed.

End GENREL.

Section PTRBINLESSDEF.

  Lemma psub_join_lessdef
    v1 v1' v2 v2' m m' v
    (LESS1: Val.lessdef v1 v1')
    (LESS2: Val.lessdef v2 v2')
    (MEXT: Mem.extends m m')
    (PSUB: psub_join m v1 v2 = v) :
  exists v', <<PSUB: psub_join m' v1' v2' = v'>> /\ <<LESS: Val.lessdef v v'>>.
Proof.
  unfold psub_join in *.
  exploit to_int_val_lessdef; try eapply LESS1; eauto. i. exploit to_int_val_lessdef; try eapply LESS2; eauto. i.
  exploit to_ptr_val_lessdef; try eapply LESS1; eauto. i. exploit to_ptr_val_lessdef; try eapply LESS2; eauto. i.
  exploit (psub_wrapper_no_angelic m v1 v2); eauto. i.
  exploit (Val.psub_inject inject_id (to_ptr_val m v1) (to_ptr_val m' v1') (to_ptr_val m v2) (to_ptr_val m' v2'));
    try rewrite val_inject_id; eauto. i.
  exploit (Val.psub_inject inject_id (to_int_val m v1) (to_int_val m' v1') (to_int_val m v2) (to_int_val m' v2'));
    try rewrite val_inject_id; eauto. i. r in H4. r in H5. rewrite val_inject_id in H4, H5. des.
  - rewrite H3 in *. destruct (classic ((Val.psub (to_int_val m v1) (to_int_val m v2)) = Vundef)).
    { rewrite H6 in *. ss. inv PSUB. esplits; eauto. }
    subst. rewrite val_join_angelic_vi; eauto.
    { eapply psub_is_only_int. }
    { eapply psub_wrapper_no_angelic; eauto. }
    { ii. rewrite H7 in *. inv H5; clarify. rewrite <- H9 in *. clarify. }
  - rewrite H3 in *. destruct (classic ((Val.psub (to_ptr_val m v1) (to_ptr_val m v2)) = Vundef)).
    { rewrite H6 in *. ss. inv PSUB. esplits; eauto. }
    subst. rewrite (val_join_angelic_vp _ Vundef); eauto.
    2:{ eapply psub_is_only_int. }
    rewrite val_join_angelic_vp; eauto.
    { eapply psub_is_only_int. }
    { eapply psub_wrapper_no_angelic; eauto. }
    { ii. rewrite H7 in *. inv H4; eauto. }
  - destruct (classic ((Val.psub (to_int_val m v1) (to_int_val m v2)) = Vundef)).
    { rewrite H3, H6 in *. ss. subst. esplits; eauto. }
    rewrite <- H3 in PSUB. rewrite val_join_same_val in PSUB.
    2:{ eapply psub_is_only_int. }
    subst. rewrite val_join_angelic_vi; eauto.
    { eapply psub_is_only_int. }
    { eapply psub_wrapper_no_angelic; eauto. }
    { ii. rewrite H7 in *. inv H5; eauto. }
Qed.

Lemma psubl_join_lessdef
    v1 v1' v2 v2' m m' v
    (LESS1: Val.lessdef v1 v1')
    (LESS2: Val.lessdef v2 v2')
    (MEXT: Mem.extends m m')
    (PSUB: psubl_join m v1 v2 = v) :
  exists v', <<PSUB: psubl_join m' v1' v2' = v'>> /\ <<LESS: Val.lessdef v v'>>.
Proof.
  unfold psubl_join in *.
  exploit to_int_val_lessdef; try eapply LESS1; eauto. i. exploit to_int_val_lessdef; try eapply LESS2; eauto. i.
  exploit to_ptr_val_lessdef; try eapply LESS1; eauto. i. exploit to_ptr_val_lessdef; try eapply LESS2; eauto. i.
  exploit (psubl_wrapper_no_angelic m v1 v2); eauto. i.
  exploit (Val.psubl_inject inject_id (to_ptr_val m v1) (to_ptr_val m' v1') (to_ptr_val m v2) (to_ptr_val m' v2'));
    try rewrite val_inject_id; eauto. i.
  exploit (Val.psubl_inject inject_id (to_int_val m v1) (to_int_val m' v1') (to_int_val m v2) (to_int_val m' v2'));
    try rewrite val_inject_id; eauto. i. r in H4. r in H5. rewrite val_inject_id in H4, H5. des.
  - rewrite H3 in *. destruct (classic ((Val.psubl (to_int_val m v1) (to_int_val m v2)) = Vundef)).
    { rewrite H6 in *. ss. inv PSUB. esplits; eauto. }
    subst. rewrite val_join_angelic_vi; eauto.
    { eapply psubl_is_only_int. }
    { eapply psubl_wrapper_no_angelic; eauto. }
    { ii. rewrite H7 in *. inv H5; clarify. rewrite <- H9 in *. clarify. }
  - rewrite H3 in *. destruct (classic ((Val.psubl (to_ptr_val m v1) (to_ptr_val m v2)) = Vundef)).
    { rewrite H6 in *. ss. inv PSUB. esplits; eauto. }
    subst. rewrite (val_join_angelic_vp _ Vundef); eauto.
    2:{ eapply psubl_is_only_int. }
    rewrite val_join_angelic_vp; eauto.
    { eapply psubl_is_only_int. }
    { eapply psubl_wrapper_no_angelic; eauto. }
    { ii. rewrite H7 in *. inv H4; eauto. }
  - destruct (classic ((Val.psubl (to_int_val m v1) (to_int_val m v2)) = Vundef)).
    { rewrite H3, H6 in *. ss. subst. esplits; eauto. }
    rewrite <- H3 in PSUB. rewrite val_join_same_val in PSUB.
    2:{ eapply psubl_is_only_int. }
    subst. rewrite val_join_angelic_vi; eauto.
    { eapply psubl_is_only_int. }
    { eapply psubl_wrapper_no_angelic; eauto. }
    { ii. rewrite H7 in *. inv H5; eauto. }
Qed.

Lemma cmpu_join_lessdef
    v1 v1' v2 v2' c m m' b
    (LESS1: Val.lessdef v1 v1')
    (LESS2: Val.lessdef v2 v2')
    (MEXT: Mem.extends m m')
    (CMP: cmpu_join m c v1 v2 = Some b) :
  <<CMP: cmpu_join m' c v1' v2' = Some b>>.
Proof.
  assert (SAMEVLD: forall b ofs, Mem.valid_pointer m b ofs = true -> Mem.valid_pointer m' b ofs = true).
  { ii. eapply Mem.valid_pointer_extends; eauto. }
  unfold cmpu_join in *.
  exploit to_int_val_lessdef; try eapply LESS1; eauto. i. exploit to_int_val_lessdef; try eapply LESS2; eauto. i.
  exploit to_ptr_val_lessdef; try eapply LESS1; eauto. i. exploit to_ptr_val_lessdef; try eapply LESS2; eauto. i.
  destruct (Val.cmpu_bool (Mem.valid_pointer m) c (to_ptr_val m v1) (to_ptr_val m v2)) eqn:PCMP.
  - destruct (Val.cmpu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2)) eqn:ICMP.
    + exploit cmpu_no_angelic; eauto. i. des; subst.
      erewrite Val.cmpu_bool_lessdef; try eapply PCMP; eauto. erewrite Val.cmpu_bool_lessdef; try eapply ICMP; eauto.
    + exploit Val.cmpu_bool_lessdef; try eapply PCMP; eauto. i. unfold to_ptr_val.
      destruct (Val.cmpu_bool (Mem.valid_pointer m') c (to_int_val m' v1') (to_int_val m' v2')) eqn:ICMP'.
      { exploit cmpu_no_angelic; eauto. i. des; subst. rewrite H3. rewrite bool_optjoin_same_bool. ss. }
      rewrite H3. ss.
  - destruct (Val.cmpu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2)) eqn:ICMP; [|ss].
    exploit Val.cmpu_bool_lessdef; try eapply ICMP; eauto. i. unfold to_int_val. rewrite H3.
    destruct (Val.cmpu_bool (Mem.valid_pointer m') c (to_ptr_val m' v1') (to_ptr_val m' v2')) eqn:PCMP'; [|ss].
    exploit cmpu_no_angelic; eauto. i. des; subst. simpl in CMP. inv CMP. eapply bool_optjoin_same_bool.
Qed.

Lemma cmplu_join_lessdef
    v1 v1' v2 v2' c m m' b
    (LESS1: Val.lessdef v1 v1')
    (LESS2: Val.lessdef v2 v2')
    (MEXT: Mem.extends m m')
    (CMP: cmplu_join m c v1 v2 = Some b) :
  <<CMP: cmplu_join m' c v1' v2' = Some b>>.
Proof.
  assert (SAMEVLD: forall b ofs, Mem.valid_pointer m b ofs = true -> Mem.valid_pointer m' b ofs = true).
  { ii. eapply Mem.valid_pointer_extends; eauto. }
  unfold cmplu_join in *.
  exploit to_int_val_lessdef; try eapply LESS1; eauto. i. exploit to_int_val_lessdef; try eapply LESS2; eauto. i.
  exploit to_ptr_val_lessdef; try eapply LESS1; eauto. i. exploit to_ptr_val_lessdef; try eapply LESS2; eauto. i.
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_ptr_val m v1) (to_ptr_val m v2)) eqn:PCMP.
  - destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2)) eqn:ICMP.
    + exploit cmplu_no_angelic; eauto. i. des; subst.
      erewrite Val.cmplu_bool_lessdef; try eapply PCMP; eauto. erewrite Val.cmplu_bool_lessdef; try eapply ICMP; eauto.
    + exploit Val.cmplu_bool_lessdef; try eapply PCMP; eauto. i. unfold to_ptr_val.
      destruct (Val.cmplu_bool (Mem.valid_pointer m') c (to_int_val m' v1') (to_int_val m' v2')) eqn:ICMP'.
      { exploit cmplu_no_angelic; eauto. i. des; subst. rewrite H3. rewrite bool_optjoin_same_bool. ss. }
      rewrite H3. ss.
  - destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2)) eqn:ICMP; [|ss].
    exploit Val.cmplu_bool_lessdef; try eapply ICMP; eauto. i. unfold to_int_val. rewrite H3.
    destruct (Val.cmplu_bool (Mem.valid_pointer m') c (to_ptr_val m' v1') (to_ptr_val m' v2')) eqn:PCMP'; [|ss].
    exploit cmplu_no_angelic; eauto. i. des; subst. simpl in CMP. inv CMP. eapply bool_optjoin_same_bool.
Qed.

End PTRBINLESSDEF.

Section PTRBININJ.

Variable f: meminj.

Lemma psubl_join_common_inject
    m1 m2 v1 v1' v2 v2' v
    (MINJ: Mem.inject f m1 m2)
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (PSUB: psubl_join_common m1 v1 v2 = v) :
  exists v', <<PSUB: psubl_join_common m2 v1' v2' = v'>> /\ <<VINJ: Val.inject f v v'>>.
Proof.
  eapply psubl_join_common_inj; eauto.
- i. eapply Mem.mi_perm; eauto. eapply Mem.mi_inj; eauto.
- i. eapply Mem.mi_src_concrete_private; eauto.
- i. eapply Mem.mi_mappedblocks; eauto.
- i. eapply Mem.mi_src_concrete_public; eauto.
- i. eapply Mem.mi_representable; eauto.
Qed.

Lemma psub_join_common_inject
    m1 m2 v1 v1' v2 v2' v
    (MINJ: Mem.inject f m1 m2)
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (PSUB: psub_join_common m1 v1 v2 = v) :
  exists v', <<PSUB: psub_join_common m2 v1' v2' = v'>> /\ <<VINJ: Val.inject f v v'>>.
Proof.
  eapply psub_join_common_inj; eauto.
- i. eapply Mem.mi_perm; eauto. eapply Mem.mi_inj; eauto.
- i. eapply Mem.mi_src_concrete_private; eauto.
- i. eapply Mem.mi_mappedblocks; eauto.
- i. eapply Mem.mi_src_concrete_public; eauto.
- i. eapply Mem.mi_representable; eauto.
Qed.

Lemma cmpu_bool_inject'
    c m1 m2 v1 v2 v1' v2' b
    (MINJ: Mem.inject f m1 m2)
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (CMP1: Val.cmpu_bool (Mem.valid_pointer m1) c v1 v2 = Some b) :
  <<CMP2: Val.cmpu_bool (Mem.valid_pointer m2) c v1' v2' = Some b>>.
Proof.
  exploit (Val.cmpu_bool_inject f (Mem.valid_pointer m1) (Mem.valid_pointer m2)); try eapply CMP1; eauto; i.
  { exploit Mem.valid_pointer_inject_val; eauto. }
  { exploit Mem.weak_valid_pointer_inject_val; eauto. }
  { exploit Mem.weak_valid_pointer_inject_no_overflow; eauto. }
  { exploit Mem.different_pointers_inject; eauto. }
Qed.

Lemma cmplu_bool_inject'
    c m1 m2 v1 v2 v1' v2' b
    (MINJ: Mem.inject f m1 m2)
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (CMP1: Val.cmplu_bool (Mem.valid_pointer m1) c v1 v2 = Some b) :
  <<CMP2: Val.cmplu_bool (Mem.valid_pointer m2) c v1' v2' = Some b>>.
Proof.
  exploit (Val.cmplu_bool_inject f (Mem.valid_pointer m1) (Mem.valid_pointer m2)); try eapply CMP1; eauto; i.
  { exploit Mem.valid_pointer_inject_val; eauto. }
  { exploit Mem.weak_valid_pointer_inject_val; eauto. }
  { exploit Mem.weak_valid_pointer_inject_no_overflow; eauto. }
  { exploit Mem.different_pointers_inject; eauto. }
Qed.

Lemma cmpu_join_inject
    c m1 m2 v1 v2 v1' v2' b
    (MINJ: Mem.inject f m1 m2)
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (CMP: cmpu_join m1 c v1 v2 = Some b) :
  <<CMP: cmpu_join m2 c v1' v2' = Some b>>.
Proof.
  unfold cmpu_join in *.
  exploit to_int_val_inject; try eapply VINJ1; eauto. i. exploit to_int_val_inject; try eapply VINJ2; eauto. i.
  exploit to_ptr_val_inject; try eapply VINJ1; eauto. i. exploit to_ptr_val_inject; try eapply VINJ2; eauto. i.
  destruct (Val.cmpu_bool (Mem.valid_pointer m1) c (to_ptr_val m1 v1) (to_ptr_val m1 v2)) eqn:PCMP.
  - destruct (Val.cmpu_bool (Mem.valid_pointer m1) c (to_int_val m1 v1) (to_int_val m1 v2)) eqn:ICMP.
    + exploit cmpu_no_angelic; eauto. i. des; subst.
      erewrite cmpu_bool_inject'; try eapply PCMP; eauto. erewrite cmpu_bool_inject'; try eapply ICMP; eauto.
    + exploit cmpu_bool_inject'; try eapply PCMP; eauto. i.
      destruct (Val.cmpu_bool (Mem.valid_pointer m2) c (to_int_val m2 v1') (to_int_val m2 v2')) eqn:ICMP'.
      { exploit cmpu_no_angelic; eauto. i. des; subst. rewrite H3. rewrite bool_optjoin_same_bool. ss. }
      rewrite H3. ss.
  - destruct (Val.cmpu_bool (Mem.valid_pointer m1) c (to_int_val m1 v1) (to_int_val m1 v2)) eqn:ICMP; [|ss].
    exploit cmpu_bool_inject'; try eapply ICMP; eauto. i. rewrite H3.
    destruct (Val.cmpu_bool (Mem.valid_pointer m2) c (to_ptr_val m2 v1') (to_ptr_val m2 v2')) eqn:PCMP'; [|ss].
    exploit cmpu_no_angelic; eauto. i. des; subst. simpl in CMP. inv CMP. eapply bool_optjoin_same_bool.
Qed.

Lemma cmplu_join_inject
    c m1 m2 v1 v2 v1' v2' b
    (MINJ: Mem.inject f m1 m2)
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (CMP: cmplu_join m1 c v1 v2 = Some b) :
  <<CMP: cmplu_join m2 c v1' v2' = Some b>>.
Proof.
  unfold cmplu_join in *.
  exploit to_int_val_inject; try eapply VINJ1; eauto. i. exploit to_int_val_inject; try eapply VINJ2; eauto. i.
  exploit to_ptr_val_inject; try eapply VINJ1; eauto. i. exploit to_ptr_val_inject; try eapply VINJ2; eauto. i.
  destruct (Val.cmplu_bool (Mem.valid_pointer m1) c (to_ptr_val m1 v1) (to_ptr_val m1 v2)) eqn:PCMP.
  - destruct (Val.cmplu_bool (Mem.valid_pointer m1) c (to_int_val m1 v1) (to_int_val m1 v2)) eqn:ICMP.
    + exploit cmplu_no_angelic; eauto. i. des; subst.
      erewrite cmplu_bool_inject'; try eapply PCMP; eauto. erewrite cmplu_bool_inject'; try eapply ICMP; eauto.
    + exploit cmplu_bool_inject'; try eapply PCMP; eauto. i.
      destruct (Val.cmplu_bool (Mem.valid_pointer m2) c (to_int_val m2 v1') (to_int_val m2 v2')) eqn:ICMP'.
      { exploit cmplu_no_angelic; eauto. i. des; subst. rewrite H3. rewrite bool_optjoin_same_bool. ss. }
      rewrite H3. ss.
  - destruct (Val.cmplu_bool (Mem.valid_pointer m1) c (to_int_val m1 v1) (to_int_val m1 v2)) eqn:ICMP; [|ss].
    exploit cmplu_bool_inject'; try eapply ICMP; eauto. i. rewrite H3.
    destruct (Val.cmplu_bool (Mem.valid_pointer m2) c (to_ptr_val m2 v1') (to_ptr_val m2 v2')) eqn:PCMP'; [|ss].
    exploit cmplu_no_angelic; eauto. i. des; subst. simpl in CMP. inv CMP. eapply bool_optjoin_same_bool.
Qed.

Lemma cmpu_join_common_inject
    c m1 m2 v1 v2 v1' v2' b
    (MINJ: Mem.inject f m1 m2)
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (CMP: cmpu_join_common m1 c v1 v2 = Some b) :
  <<CMP: cmpu_join_common m2 c v1' v2' = Some b>>.
Proof.
  eapply cmpu_join_common_inj; eauto.
- i. eapply Mem.mi_perm; eauto. eapply Mem.mi_inj; eauto.
- i. eapply Mem.valid_pointer_inject_val; eauto.
- i. eapply Mem.weak_valid_pointer_inject_val; eauto.
- i. eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
- i. eapply Mem.different_pointers_inject; eauto.
- i. eapply Mem.mi_src_concrete_private; eauto.
- i. eapply Mem.mi_mappedblocks; eauto.
- i. eapply Mem.mi_src_concrete_public; eauto.
- i. eapply Mem.mi_representable; eauto.
Qed.

Lemma cmplu_join_common_inject
    c m1 m2 v1 v2 v1' v2' b
    (MINJ: Mem.inject f m1 m2)
    (VINJ1: Val.inject f v1 v1')
    (VINJ2: Val.inject f v2 v2')
    (CMP: cmplu_join_common m1 c v1 v2 = Some b) :
  <<CMP: cmplu_join_common m2 c v1' v2' = Some b>>.
Proof.
  eapply cmplu_join_common_inj; eauto.
- i. eapply Mem.mi_perm; eauto. eapply Mem.mi_inj; eauto.
- i. eapply Mem.valid_pointer_inject_val; eauto.
- i. eapply Mem.weak_valid_pointer_inject_val; eauto.
- i. eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
- i. eapply Mem.different_pointers_inject; eauto.
- i. eapply Mem.mi_src_concrete_private; eauto.
- i. eapply Mem.mi_mappedblocks; eauto.
- i. eapply Mem.mi_src_concrete_public; eauto.
- i. eapply Mem.mi_representable; eauto.
Qed.

End PTRBININJ.

Section MemRel.

Lemma perm_concrete_extends
    m1 m2 b ofs k p
    (CE: concrete_extends m1 m2)
    (PERM: Mem.perm m1 b ofs k p):
  <<PERM: Mem.perm m2 b ofs k p>>.
Proof. inv CE. eauto. Qed.

Lemma range_perm_concrete_extends
    m1 m2 b lo hi k p
    (CE: concrete_extends m1 m2)
    (PERM: Mem.range_perm m1 b lo hi k p):
  <<PERM: Mem.range_perm m2 b lo hi k p>>.
Proof. ii. eapply perm_concrete_extends; eauto. Qed.

Lemma valid_access_concrete_extends
    m1 m2 chunk b ofs p
    (CE: concrete_extends m1 m2)
    (PERM: Mem.valid_access m1 chunk b ofs p):
  <<PERM: Mem.valid_access m2 chunk b ofs p>>.
Proof. unfold Mem.valid_access in *. des. split; auto. eapply range_perm_concrete_extends; eauto. Qed.

Lemma same_conc_val_intptr m1 m2 v1 v2
    (SAME: m1.(Mem.mem_concrete) = m2.(Mem.mem_concrete)) (BIND: val_intptr m1 v1 v2) :
  <<BIND: val_intptr m2 v1 v2>>.
Proof.
  inv BIND; try by econs. econs; eauto. ss; unfold Mem.ptr2int_v, Mem.ptr2int in *. des_ifs_safe.
  rewrite <- SAME. des_ifs.
Qed.

Lemma store_val_intptr chunk m1 m2 b ofs v v1 v2
    (STORE:Mem.store chunk m1 b ofs v = Some m2) (BIND: val_intptr m1 v1 v2) :
  <<BIND: val_intptr m2 v1 v2>>.
Proof. eapply Mem.concrete_store in STORE. eapply same_conc_val_intptr; eauto. Qed.

Lemma free_val_intptr m1 m2 b lo hi v1 v2
    (FREE: Mem.free m1 b lo hi = Some m2) (BIND: val_intptr m1 v1 v2) :
  <<BIND: val_intptr m2 v1 v2>>.
Proof. eapply Mem.concrete_free in FREE. eapply same_conc_val_intptr; eauto. Qed.

Lemma alloc_val_intptr m1 m2 b lo hi v1 v2
    (ALLOC: Mem.alloc m1 lo hi = (m2, b)) (BIND: val_intptr m1 v1 v2) :
  <<BIND: val_intptr m2 v1 v2>>.
Proof. eapply Mem.concrete_alloc in ALLOC. eapply same_conc_val_intptr; eauto. Qed.

Lemma same_concrete_memval_intptr
    m1 m2 mv1 mv2
    (SAME: m1.(Mem.mem_concrete) = m2.(Mem.mem_concrete))
    (BIND: memval_intptr m1 mv1 mv2) :
  <<BIND: memval_intptr m2 mv1 mv2>>.
Proof.
  inv BIND; ss; try by econs.
  - econs; eauto. ss. unfold Mem.ptr2int in *. rewrite <- SAME. ss.
  - econs; eauto. eapply same_conc_val_intptr; eauto.
Qed.

Lemma same_concrete_memval_intptr_list
    m1 m2 mvl1 mvl2
    (SAME: m1.(Mem.mem_concrete) = m2.(Mem.mem_concrete))
    (BIND: list_forall2 (memval_intptr m1) mvl1 mvl2) :
  <<BIND: list_forall2 (memval_intptr m2) mvl1 mvl2>>.
Proof.
  ginduction BIND; ss; i; [econs|].
  econs; eauto; [eapply same_concrete_memval_intptr; eauto|].
  eapply IHBIND; eauto.
Qed.

Lemma concrete_extends_perm
    m1 m2 b ofs k p
    (CE: concrete_extends m1 m2)
    (PERM: Mem.perm m1 b ofs k p):
  <<PERM: Mem.perm m2 b ofs k p>>.
Proof. inv CE; eauto. Qed.

Lemma concrete_extends_range_perm
    m1 m2 b lo hi k p
    (CE: concrete_extends m1 m2)
    (PERM: Mem.range_perm m1 b lo hi k p):
  <<PERM: Mem.range_perm m2 b lo hi k p>>.
Proof. ii. eapply concrete_extends_perm; eauto. Qed.

Lemma getN_concrete_extends
    m1 m2 b ofs n 
    (CE: concrete_extends m1 m2)
    (PERM: Mem.range_perm m1 b ofs (ofs + Z.of_nat n) Cur Readable):
  <<BINDED: list_forall2 (memval_intptr m2) (Mem.getN n ofs (Mem.mem_contents m1) # b) (Mem.getN n ofs (Mem.mem_contents m2) # b)>>.
Proof.
  revert PERM. revert ofs.
  ginduction n; ss; ii; [econs|]. econs.
- inv CE. eapply extended_contents0. eapply PERM. lia.
- eapply IHn; eauto. ii. eapply PERM. lia.
Qed.

Lemma byte_memval_intptr_byte
    m2 vl1 vl2 bl1
    (BIND : list_forall2 (memval_intptr m2) vl1 vl2)
    (PB1 : proj_bytes vl1 = Some bl1) :
  <<PB2: exists bl2, proj_bytes vl2 = Some bl2 /\ bl1 = bl2>>.
Proof.
  ginduction BIND; ss; i.
  { clarify. esplits; eauto. }
  des_ifs; try by inv H.
  2:{ exploit IHBIND; eauto. i. des; clarify. }
  inv H. exploit IHBIND; eauto. i. des; clarify. esplits; eauto.
Qed.

(* Lemma pure_memval_intptr_pure *)
(*   vl1 vl2 m *)
(*   (UNDEF: ~ In Undef vl1) *)
(*   (PURE: bytes_not_pure vl1 = false) *)
(*   (BIND: list_forall2 (memval_intptr m) vl1 vl2) : *)
(*   <<PURE: bytes_not_pure vl2 = false>>. *)
(* Proof. *)
(*   ginduction BIND; ss; i. *)
(*   exploit IHBIND; eauto. i. *)
(*   (* false : mix of two different pointer fragment in src - one pointer is captured byte in tgt *) *)
(* Abort. *)

Lemma inj_bytes_all_bytes bl:
  <<BYTES: forallb is_byte_mv (inj_bytes bl) = true>>.
Proof. ginduction bl; ss. Qed.

Lemma setN_concrete_extends
    (access: Z -> Prop) m vl1 vl2
    (BIND: list_forall2 (memval_intptr m) vl1 vl2)
    p c1 c2
    (SRC: forall q, access q -> memval_intptr m (ZMap.get q c1) (ZMap.get q c2)):
  (forall q, access q -> memval_intptr m (ZMap.get q (Mem.setN vl1 p c1))
                                   (ZMap.get q (Mem.setN vl2 p c2))).
Proof.
  ginduction BIND; ii; ss; eauto.
  eapply IHBIND; eauto.
  i. rewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p).
  { subst q0. rewrite ZMap.gss. auto. }
  rewrite ZMap.gso. auto. unfold ZIndexed.t in *. lia.
Qed.

Lemma proj_bytes_binded m vl1 vl2 bl
    (BIND: list_forall2 (memval_intptr m) vl1 vl2)
    (BYTES: proj_bytes vl1 = Some bl) :
  <<BYTES: proj_bytes vl2 = Some bl>>.
Proof.
  ginduction BIND; ss; i. des_ifs_safe. erewrite IHBIND; eauto. inv H; ss.
Qed.

Lemma intptr_val_intptr_intptr m vl1 vl2
    (BIND: list_forall2 (memval_intptr m) vl1 vl2)
    (IP: forallb Mem.is_intptr_mv vl1 = true):
  <<IP: forallb Mem.is_intptr_mv vl2 = true>>.
Proof.
  ginduction BIND; ss. i.
  eapply andb_prop in IP. des. rewrite IHBIND; eauto.
  clear IHBIND. unfold Mem.is_intptr_mv in *. des_ifs; ss; inv H; inv H1.
  repeat rewrite andb_true_iff in IP. des; subst. rewrite IP, IP1. auto.
Qed.

Lemma bytes_binded_bytes m vl1 vl2
    (BIND: list_forall2 (memval_intptr m) vl1 vl2)
    (BYTE: forallb is_byte_mv vl1 = true):
  <<BYTE: forallb is_byte_mv vl2 = true /\ vl1 = vl2>>.
Proof.
  ginduction BIND; ss. i.
  eapply andb_prop in BYTE. des. exploit IHBIND; eauto. i. des. subst.
  clear IHBIND. unfold is_byte_mv in *. des_ifs; ss; inv H. esplits; eauto.
Qed.

Lemma ptrlike_binded_ptrlike m vl1 vl2
    (BIND: list_forall2 (memval_intptr m) vl1 vl2)
    (PL: forallb Mem.is_ptrlike_mv vl1 = true):
  <<PL: forallb Mem.is_ptrlike_mv vl2 = true>>.
Proof.
  ginduction BIND; ss. i.
  eapply andb_prop in PL. des. rewrite IHBIND; eauto.
  clear IHBIND. unfold Mem.is_ptrlike_mv in *. des_ifs; ss; inv H; ss. des_ifs; inv H0.
  all: destruct q; ss.
Qed.

Lemma notptr_binded_notptr m vl1 vl2
    (BIND: list_forall2 (memval_intptr m) vl1 vl2)
    (PTRL: forallb Mem.is_ptrlike_mv vl1 = true)
    (IP: forallb is_ptr_mv vl1 = false):
  <<IP: forallb is_ptr_mv vl2 = false>>.
Proof.
  ginduction BIND; ss. i.
  rewrite andb_false_iff in IP. des.
  { destruct a1; ss; [inv H; ss|]. des_ifs; inv H; inv H4; ss. des_ifs. }
  erewrite IHBIND; eauto.
  2:{ eapply andb_prop in PTRL; des. eauto. }
  eapply andb_false_r.
Qed.

Lemma mixed_bind_mixed m vl1 vl2
    (BIND: list_forall2 (memval_intptr m) vl1 vl2)
    (MIX: Mem.is_mixed_mvs vl1 = true) : 
  <<MIX: Mem.is_mixed_mvs vl2 = true>>.
Proof.
  unfold Mem.is_mixed_mvs in *. eapply andb_prop in MIX. des.
  exploit ptrlike_binded_ptrlike; eauto. i. rewrite H. ss.
  rewrite negb_true_iff in MIX0. erewrite notptr_binded_notptr; eauto.
Qed.

Lemma normalize_check_bind_normalize_check
    chunk m1 m2 vl1 vl2
    (CE: concrete_extends m1 m2)
    (BIND: list_forall2 (memval_intptr m2) vl1 vl2)
    (MIX: Mem.normalize_check chunk vl1 = true) : 
  <<MIX: Mem.normalize_check chunk vl2 = true>>.
Proof.
  unfold Mem.normalize_check in *. des_ifs; eapply andb_prop in MIX; des;
  erewrite mixed_bind_mixed; eauto.
Qed.

Lemma check_value_is_ptr n b ofs vl
    (CHECK: check_value n (Vptr b ofs) Q64 vl = true):
  <<PTR: forallb is_ptr_mv vl = true>>.
Proof.
  ginduction n; ss; i; des_ifs.
  des_ifs. repeat rewrite andb_true_iff in CHECK. des.
  destruct v; destruct q; ss. des_ifs. erewrite IHn; eauto.
Qed.

Lemma check_value_not_ptrlike n' n v vl
    (NOTPTR: Mem.is_ptrlike_mv (Fragment v Q64 n') = false)
    (CHECK: check_value n v Q64 vl = true):
  <<PTR: forallb (fun mv => (negb (Mem.is_ptrlike_mv mv))) vl = true>>.
Proof.
  ginduction n; ss; i; des_ifs. des_ifs. InvBooleans. subst.
  simpl. erewrite IHn; eauto. unfold Mem.is_ptrlike_mv in *. clear - NOTPTR. ss. des_ifs.
Qed.

(* move to memory.v *)
Lemma normalize_fail chunk m vl
    (MIX: Mem.normalize_check chunk vl = true)
    (FAIL: forallb is_byte_mv (Mem.normalize_mvs chunk m vl) = false) :
  <<UNDEF: decode_val chunk (Mem.normalize_mvs chunk m vl) = Vundef>>.
Proof.
  unfold decode_val. rewrite Mem.not_bytes_proj_bytes_fail; eauto.
  unfold Mem.normalize_mvs in *. rewrite MIX in *. des_ifs.
  - destruct vl as [| mv vl]; [ss|]. simpl in FAIL. destruct mv; simpl in FAIL; try by (ss; eauto).
    des_ifs.
    { destruct v; try by (ss; clarify).
      - simpl in Heq0. clarify. simpl. des_ifs_safe. exfalso. ss. rewrite Heq1 in Heq0. clear - Heq1 Heq0.
        subst. eapply nth_error_in in Heq1. unfold rev_if_be_mv in Heq1. des_ifs.
        rewrite <- in_rev in Heq1. eapply Mem.inj_bytes_no_fragment; eauto. rewrite encode_int_length. lia.
      - simpl in Heq0. clarify. simpl. des_ifs_safe. exfalso. ss. clear - Heq0.
        subst. eapply nth_error_in in Heq0. unfold rev_if_be_mv in Heq0. des_ifs.
        rewrite <- in_rev in Heq0. eapply Mem.inj_bytes_no_fragment; eauto. rewrite encode_int_length. lia. }
    { unfold Mem._decode_normalize_mv. simpl. rewrite Heq0, Heq1.
      destruct v; simpl in Heq0; clarify; des_ifs_safe.
      - repeat rewrite andb_true_iff in Heq0. des. clarify.
      - repeat rewrite andb_true_iff in Heq2. des. clarify. }
    { simpl in FAIL. destruct v; simpl in Heq0; clarify. des_ifs.
      (* proj val success -> all ptr -> not mixed. see Mem.long_proj_long_fragment *)
      destruct (check_value (size_quantity_nat Q64) (Vptr b i) Q64 (map (Mem._decode_normalize_mv m) (Fragment (Vptr b i) q n :: vl))) eqn: CHECK'.
      2:{ unfold proj_value. des_ifs. simpl in Heq2. des_ifs. }
      destruct (check_value (size_quantity_nat Q64) (Vptr b i) q (map (Mem._decode_normalize_mv m) (Fragment (Vptr b i) q n :: vl))) eqn: CHECK.
      2:{ unfold proj_value. des_ifs. simpl in Heq2. des_ifs.
          assert (q0 = Q64).
          { simpl in Heq3. repeat rewrite andb_true_iff in Heq3. des. destruct q0; ss. }
          subst. clarify. }
      assert (forallb is_ptr_mv (map (Mem._decode_normalize_mv m) (Fragment (Vptr b i) q n :: vl)) = true).
      { eapply check_value_is_ptr; eauto. }
      clear CHECK'.
      assert (forallb is_ptr_mv (Fragment (Vptr b i) q n :: vl) = true).
      { (* make lemma *)
        rewrite forallb_forall in *. ii. eapply in_map with (f:= (Mem._decode_normalize_mv m)) in H0.
        eapply H in H0. clear - H0. destruct x; ss. unfold Mem.to_int in H0.
        destruct v; try by ss.
        - ss. des_ifs. specialize (inj_bytes_all_bytes (encode_int 4 (Int.unsigned i))). i.
          eapply nth_error_In in Heq. unfold rev_if_be_mv in *. des_ifs. ss.
          r in H. rewrite <- in_rev in Heq. rewrite forallb_forall in H. eapply H in Heq. destruct m0; ss.
        - ss. des_ifs. specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned i))). i.
          eapply nth_error_In in Heq. unfold rev_if_be_mv in *. des_ifs. ss.
          r in H. rewrite <- in_rev in Heq. rewrite forallb_forall in H. eapply H in Heq. destruct m0; ss.
        - ss. des_ifs. ss. specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned (Int64.repr z)))). i.
          eapply nth_error_In in Heq1. unfold rev_if_be_mv in *. des_ifs. ss.
          r in H. rewrite <- in_rev in Heq1. rewrite forallb_forall in H. eapply H in Heq1. destruct m0; ss. }
      unfold Mem.normalize_check, Mem.is_mixed_mvs in MIX. rewrite H0 in MIX.
      repeat rewrite andb_true_iff in MIX. des. ss. }
  - destruct vl as [| mv vl]; [ss|]. simpl in FAIL. destruct mv; simpl in FAIL; try by (ss; eauto).
    des_ifs.
    { destruct v; try by (ss; clarify).
      - simpl in Heq. clarify. simpl. des_ifs_safe. exfalso. ss. rewrite Heq0 in Heq. clear - Heq Heq0.
        subst. eapply nth_error_in in Heq0. unfold rev_if_be_mv in Heq0. des_ifs.
        rewrite <- in_rev in Heq0. eapply Mem.inj_bytes_no_fragment; eauto. rewrite encode_int_length. lia.
      - simpl in Heq. clarify. simpl. des_ifs_safe. exfalso. ss. clear - Heq.
        subst. eapply nth_error_in in Heq. unfold rev_if_be_mv in Heq. des_ifs.
        rewrite <- in_rev in Heq. eapply Mem.inj_bytes_no_fragment; eauto. rewrite encode_int_length. lia. }
    { unfold Mem._decode_normalize_mv. simpl. rewrite Heq, Heq0.
      destruct v; simpl in Heq; clarify; des_ifs_safe.
      - repeat rewrite andb_true_iff in Heq. des. clarify.
      - repeat rewrite andb_true_iff in Heq1. des. clarify. }
    { simpl in FAIL. destruct v; simpl in Heq; clarify. des_ifs.
      (* proj val success -> all ptr -> not mixed. see Mem.long_proj_long_fragment *)
      destruct (check_value (size_quantity_nat Q64) (Vptr b i) Q64 (map (Mem._decode_normalize_mv m) (Fragment (Vptr b i) q n :: vl))) eqn: CHECK'.
      2:{ unfold proj_value. des_ifs. simpl in Heq1. des_ifs. }
      destruct (check_value (size_quantity_nat Q64) (Vptr b i) q (map (Mem._decode_normalize_mv m) (Fragment (Vptr b i) q n :: vl))) eqn: CHECK.
      2:{ unfold proj_value. des_ifs. simpl in Heq1. des_ifs.
          assert (q0 = Q64).
          { simpl in Heq2. repeat rewrite andb_true_iff in Heq2. des. destruct q0; ss. }
          subst. clarify. }
      assert (forallb is_ptr_mv (map (Mem._decode_normalize_mv m) (Fragment (Vptr b i) q n :: vl)) = true).
      { eapply check_value_is_ptr; eauto. }
      clear CHECK'.
      assert (forallb is_ptr_mv (Fragment (Vptr b i) q n :: vl) = true).
      { (* make lemma *)
        rewrite forallb_forall in *. ii. eapply in_map with (f:= (Mem._decode_normalize_mv m)) in H0.
        eapply H in H0. clear - H0. destruct x; ss. unfold Mem.to_int in H0.
        destruct v; try by ss.
        - ss. des_ifs. specialize (inj_bytes_all_bytes (encode_int 4 (Int.unsigned i))). i.
          eapply nth_error_In in Heq. unfold rev_if_be_mv in *. des_ifs. ss.
          r in H. rewrite <- in_rev in Heq. rewrite forallb_forall in H. eapply H in Heq. destruct m0; ss.
        - ss. des_ifs. specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned i))). i.
          eapply nth_error_In in Heq. unfold rev_if_be_mv in *. des_ifs. ss.
          r in H. rewrite <- in_rev in Heq. rewrite forallb_forall in H. eapply H in Heq. destruct m0; ss.
        - ss. des_ifs. ss. specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned (Int64.repr z)))). i.
          eapply nth_error_In in Heq1. unfold rev_if_be_mv in *. des_ifs. ss.
          r in H. rewrite <- in_rev in Heq1. rewrite forallb_forall in H. eapply H in Heq1. destruct m0; ss. }
      unfold Mem.normalize_check, Mem.is_mixed_mvs in MIX. rewrite H0 in MIX.
      repeat rewrite andb_true_iff in MIX. des. ss. }
Qed.

Lemma binded_normalize_binded m1 m2 vl1 vl2 chunk
    (CE : concrete_extends m1 m2)
    (UNDEF1 : ~ In Undef vl1)
    (UNDEF2 : forall q n, ~ In (Fragment Vundef q n) vl1)
  (BIND : list_forall2 (memval_intptr m2) vl1 vl2):
  <<BIND: list_forall2 (memval_intptr m2) (Mem.normalize_mvs chunk m1 vl1) (Mem.normalize_mvs chunk m2 vl2)>>.
Proof.
  destruct (Mem.normalize_check chunk vl1) eqn:MIXED1.
  { exploit normalize_check_bind_normalize_check; eauto. intros MIXED2.
    unfold Mem.normalize_mvs. rewrite MIXED1, MIXED2.
    assert (PTRL1: forallb Mem.is_ptrlike_mv vl1 = true).
    { clear - MIXED1. unfold Mem.normalize_check, Mem.is_mixed_mvs in MIXED1. des_ifs; ss.
      - do 2 rewrite andb_true_iff in *. des; eauto.
      - do 2 rewrite andb_true_iff in *. des; eauto. }
    clear MIXED1 MIXED2.
    ginduction BIND; i; ss; [econs|].
    econs; eauto.
    2:{ eapply IHBIND; eauto. ii. eapply UNDEF2. eauto. eapply andb_prop in PTRL1. des; eauto. }
    inv H; ss; try by econs.
    - des_ifs; try by econs.
      2:{ ss. rewrite nth_error_None in Heq0.
          assert (z = z0).
          { unfold Mem.ptr2int in *. des_ifs. eapply extended_concrete in Heq3; eauto. clarify. }
          subst. exploit nth_error_Some. erewrite H3. ii. inv H. exploit H1; eauto; ii; clarify. lia. }
      2:{ econs; eauto; ss.
          - ss. rewrite Heq2. des_ifs.
          - ss. }
      assert (z = z0).
      { unfold Mem.ptr2int in *. des_ifs. eapply extended_concrete in Heq3; eauto. clarify. }
      subst. ss. clarify. econs.
    - inv H0; ss; try by (econs; econs).
      + eapply memval_intptr_refl.
      + unfold Mem.ptr2int.
        destruct ((Mem.mem_concrete m1) ! b) eqn:CONC1; cycle 1.
        { destruct ((Mem.mem_concrete m2) ! b) eqn:CONC2; cycle 1.
          { eapply memval_intptr_refl. }
          des_ifs; cycle 1.
          { eapply memval_intptr_refl. }
          ss. dup Heq.
          unfold rev_if_be_mv in Heq1. des_ifs. eapply nth_error_In in Heq1.
          rewrite <- in_rev in Heq1. 
          specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned (Int64.repr (z + Ptrofs.unsigned ofs))))).
          i. des. rewrite forallb_forall in H. exploit H; eauto. i. destruct m; ss.
          exploit memval_intptr_byte_frag64; eauto.
          { instantiate (2:=m2). unfold Mem.to_int. ss. unfold Mem.ptr2int. rewrite CONC2. instantiate (2:=ofs).
            des_ifs. }
          { unfold Mptr. des_ifs. ss. eauto. }
          i. eauto. eapply andb_prop in PTRL1. des. destruct q; ss. }
        eapply extended_concrete in CONC1; eauto. rewrite CONC1. eapply memval_intptr_refl.
      + des_ifs_safe.
        destruct (Mem.ptr2int b (Ptrofs.unsigned ofs) m1) eqn:P.
        2:{ des_ifs.
            2:{ econs. econs; eauto. ss. unfold Mem.ptr2int_v. rewrite Heq. ss. }
            unfold rev_if_be_mv in Heq0. des_ifs. (* unfold Mem.ptr2int in Heq. des_ifs. *)
            assert (exists byt, m = Byte byt).
            { eapply nth_error_In in Heq0. rewrite <- in_rev in Heq0. clear - Heq0.
              specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned (Int64.repr z)))). i.
              r in H. rewrite forallb_forall in H. eapply H in Heq0. destruct m; ss. eauto. }
            des. subst.
            assert (q = Q64).
            { eapply andb_prop in PTRL1. des. clear - PTRL1. destruct q; ss. }
            subst. exploit memval_intptr_byte_frag64; eauto.
            { ss. erewrite Heq. ss. }
            { unfold rev_if_be_mv. des_ifs. } }
        ss. assert (z = z0).
        { unfold Mem.ptr2int in *. des_ifs. eapply extended_concrete in Heq0; eauto. clarify. }
        subst. des_ifs.
        { eapply memval_intptr_refl. }
        econs; eauto. econs; eauto. ss. rewrite Heq. ss. }
  destruct (Mem.normalize_check chunk vl2) eqn:MIXED2.
  2:{ unfold Mem.normalize_mvs. des_ifs. }
  unfold Mem.normalize_mvs. rewrite MIXED1, MIXED2.
  assert (forallb is_ptr_mv vl1 = true).
  { unfold Mem.normalize_check in *. des_ifs.
    - eapply andb_prop in MIXED2. des. rewrite MIXED2 in MIXED1. ss.
      eapply andb_prop in MIXED0. des.
      assert (forallb Mem.is_ptrlike_mv vl1 = true).
      { clear MIXED3 MIXED1. ginduction BIND; ss. ii. rewrite andb_true_iff in *. des. split.
        { inv H; ss.
          - inv H0; ss.
            2:{ exfalso. eapply UNDEF2. eauto. }
            des_ifs. ss. clear - MIXED0. unfold Mem.is_ptrlike_mv in *. ss. des_ifs. destruct q; ss.
          - exfalso. eapply UNDEF2. eauto.
          - exfalso. eapply UNDEF1. eauto. }
        eapply IHBIND; eauto. ii. eapply UNDEF2. eauto. }
      unfold Mem.is_mixed_mvs in MIXED1. rewrite H in MIXED1. ss. rewrite negb_false_iff in MIXED1. ss.
    - eapply andb_prop in MIXED2. des. rewrite MIXED2 in MIXED1. ss.
      eapply andb_prop in MIXED0. des.
      assert (forallb Mem.is_ptrlike_mv vl1 = true).
      { clear MIXED3 MIXED1. ginduction BIND; ss. ii. rewrite andb_true_iff in *. des. split.
        { inv H; ss.
          - inv H0; ss.
            2:{ exfalso. eapply UNDEF2. eauto. }
            des_ifs. ss. clear - MIXED0. unfold Mem.is_ptrlike_mv in *. ss. des_ifs. destruct q; ss.
          - exfalso. eapply UNDEF2. eauto.
          - exfalso. eapply UNDEF1. eauto. }
        eapply IHBIND; eauto. ii. eapply UNDEF2. eauto. }
      unfold Mem.is_mixed_mvs in MIXED1. rewrite H in MIXED1. ss. rewrite negb_false_iff in MIXED1. ss. }
  clear MIXED1 MIXED2.
  ginduction BIND; ss; ii; [econs|].
  eapply andb_prop in H0. des. econs; eauto.
  2:{ eapply IHBIND; eauto. ii. eapply UNDEF2; eauto. }
  inv H; try by ss.
  - econs; eauto.
  - simpl in H0. des_ifs. inv H2; ss.
    + des_ifs; try by (econs; econs). ss.
      assert (exists b, m = Byte b).
      { specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned (Int64.repr z)))). i.
        r in H. eapply nth_error_In in Heq1. rewrite forallb_forall in H.
        unfold rev_if_be_mv in Heq1. des_ifs. rewrite <- in_rev in Heq1.
        eapply H in Heq1. destruct m; ss. eauto. }
      des. subst. destruct q; ss. econs; eauto.
      { ss. rewrite Heq2. des_ifs. }
      ss.
    + des_ifs.
      2:{ econs; eauto. econs; eauto. ss; unfold Mem.ptr2int_v. rewrite Heq1. ss. }
      assert (exists b, m = Byte b).
      { specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned (Int64.repr z)))). i.
        r in H. eapply nth_error_In in Heq0. rewrite forallb_forall in H.
        unfold rev_if_be_mv in Heq0. des_ifs. rewrite <- in_rev in Heq0.
        eapply H in Heq0. destruct m; ss. eauto. }
      des. subst. destruct q; ss. econs; eauto.
      { ss. rewrite Heq1. des_ifs. }
      ss.
Qed.

Lemma not_ptrlike_not_normalize chunk vl
    (PTRL: forallb Mem.is_ptrlike_mv vl = false):
  <<NORM: Mem.normalize_check chunk vl = false>>.
Proof.
  unfold Mem.normalize_check, Mem.is_mixed_mvs. rewrite PTRL. ss. des_ifs.
Qed.

Lemma remove_inj_byte l1 l2
    (BYTE: map Byte l1 = map Byte l2): l1 = l2.
Proof.
  ginduction l1; ss; i; [destruct l2; ss|].
  destruct l2; ss. clarify. erewrite IHl1; eauto.
Qed.

Lemma ptr_byte_binded vl1 vl2 chunk m
  (CHUNK: chunk = Mint64 \/ chunk = Many64)
  (LEN: ((Datatypes.length vl1) > 0)%nat)
  (PTR : forallb is_ptr_mv vl1 = true)
  (BYTE: forallb is_byte_mv vl2 = true)
  (BIND: list_forall2 (memval_intptr m) vl1 vl2):
  <<BIND: val_intptr m (decode_val chunk vl1) (decode_val chunk vl2)>>.
Proof.
  unfold decode_val.
  assert (PB1: proj_bytes vl1 = None).
  { clear - LEN PTR. ginduction vl1; ss; i; [lia|]. des_ifs; ss. }
  assert (PB2: exists bl2, proj_bytes vl2 = Some bl2).
  { clear - BYTE. ginduction vl2; ss; i.
    - esplits; eauto.
    - eapply andb_prop in BYTE. des. exploit IHvl2; eauto. i. des. des_ifs. esplits; eauto. }
  des; rewrite PB1, PB2; subst; ss.
  - des_ifs; try by econs.
    { unfold proj_value in Heq0. des_ifs. }
    unfold proj_value in Heq0. des_ifs.
    econs; eauto. simpl. unfold Mem.ptr2int_v. des_ifs.
    2:{ inv BIND. inv H1; try by ss. simpl in H7. des_ifs. }
    assert (bl2 = (encode_int 8 (Int64.unsigned (Int64.repr z)))).
    { simpl in Heq1.
      (* 7 *)
      repeat rewrite andb_true_iff in Heq1. des. destruct q; ss.
      assert (n = 7%nat) by (clear - Heq3; des_ifs). subst.
      (* 6 *)
      destruct l; clarify. destruct m0; ss. des_ifs_safe.
      repeat rewrite andb_true_iff in Heq2. des. destruct q; ss.
      assert (n = 6%nat) by (clear - Heq6; des_ifs). subst.
      (* 5 *)
      destruct l; clarify. destruct m0; ss. des_ifs_safe.
      repeat rewrite andb_true_iff in Heq5. des. destruct q; ss.
      assert (n = 5%nat) by (clear - Heq9; des_ifs). subst.
      (* 4 *)
      destruct l; clarify. destruct m0; ss. des_ifs_safe.
      repeat rewrite andb_true_iff in Heq8. des. destruct q; ss.
      assert (n = 4%nat) by (clear - Heq12; des_ifs). subst.
      (* 3 *)
      destruct l; clarify. destruct m0; ss. des_ifs_safe.
      repeat rewrite andb_true_iff in Heq11. des. destruct q; ss.
      assert (n = 3%nat) by (clear - Heq15; des_ifs). subst.
      (* 2 *)
      destruct l; clarify. destruct m0; ss. des_ifs_safe.
      repeat rewrite andb_true_iff in Heq14. des. destruct q; ss.
      assert (n = 2%nat) by (clear - Heq18; des_ifs). subst.
      (* 1 *)
      destruct l; clarify. destruct m0; ss. des_ifs_safe.
      repeat rewrite andb_true_iff in Heq17. des. destruct q; ss.
      assert (n = 1%nat) by (clear - Heq21; des_ifs). subst.
      (* 0 *)
      destruct l; clarify. destruct m0; ss. des_ifs_safe.
      repeat rewrite andb_true_iff in Heq20. des. destruct q; ss.
      assert (n = 0%nat) by (clear - Heq24; des_ifs). subst.
      des_ifs_safe.
      eapply proj_sumbool_true in Heq1, Heq2, Heq5, Heq8, Heq11, Heq14, Heq17, Heq20.
      clarify.
      inv BIND. inv H1; ss. unfold Mptr in *. des_ifs_safe.
      inv H3. inv H1; ss. unfold Mptr in *. des_ifs_safe.
      rewrite Heq2 in Heq8. clarify.
      inv H5. inv H1; ss. unfold Mptr in *. des_ifs_safe.
      rewrite Heq2 in Heq0. clarify.
      inv H6. inv H1; ss. unfold Mptr in *. des_ifs_safe.
      rewrite Heq2 in Heq0. clarify.
      inv H7. inv H1; ss. unfold Mptr in *. des_ifs_safe.
      rewrite Heq2 in Heq0. clarify.
      inv H8. inv H1; ss. unfold Mptr in *. des_ifs_safe.
      rewrite Heq2 in Heq0. clarify.
      inv H9. inv H1; ss. unfold Mptr in *. des_ifs_safe.
      rewrite Heq2 in Heq0. clarify.
      inv H10. inv H1; ss. unfold Mptr in *. des_ifs_safe.
      rewrite Heq2 in Heq0. clarify.
      inv H11. ss. clarify. unfold rev_if_be_mv in *. des_ifs.
      assert (l0 = []); subst.
      { destruct l0; ss. }
      assert (rev (rev (inj_bytes (encode_int 8 (Int64.unsigned (Int64.repr z))))) =
                rev [Byte bt6; Byte bt5; Byte bt4; Byte bt3; Byte bt2; Byte bt1; Byte bt0; Byte bt]).
      { rewrite Heq2. ss. }
      clear Heq2. rewrite rev_involutive in H. ss. unfold inj_bytes in H.
      replace [Byte bt; Byte bt0; Byte bt1; Byte bt2; Byte bt3; Byte bt4; Byte bt5; Byte bt6] with
        (map Byte [bt; bt0; bt1; bt2; bt3; bt4; bt5; bt6]) in H by ss.
      eapply remove_inj_byte; eauto. }
    subst. erewrite decode_encode_int_8; eauto.
  - unfold proj_value. des_ifs; [| econs]. simpl in PTR. des_ifs_safe. destruct q; try by ss.
    eapply andb_prop in PTR. des. clear PTR.
    econs; eauto. simpl. unfold Mem.ptr2int_v. des_ifs.
    2:{ inv BIND. inv H1; try by ss. simpl in H5. des_ifs. }
    assert (bl2 = (encode_int 8 (Int64.unsigned (Int64.repr z)))).
    { simpl in Heq.
      (* 7 *)
      repeat rewrite andb_true_iff in Heq. des. (* destruct q; ss. *)
      assert (n = 7%nat) by (clear - Heq3; des_ifs). subst.
      (* 6 *)
      destruct l; clarify. destruct m0; ss. des_ifs_safe.
      repeat rewrite andb_true_iff in Heq2. des. destruct q; ss.
      assert (n = 6%nat) by (clear - Heq6; des_ifs). subst.
      (* 5 *)
      destruct l; clarify. destruct m0; ss. des_ifs_safe.
      repeat rewrite andb_true_iff in Heq5. des. destruct q; ss.
      assert (n = 5%nat) by (clear - Heq9; des_ifs). subst.
      (* 4 *)
      destruct l; clarify. destruct m0; ss. des_ifs_safe.
      repeat rewrite andb_true_iff in Heq8. des. destruct q; ss.
      assert (n = 4%nat) by (clear - Heq12; des_ifs). subst.
      (* 3 *)
      destruct l; clarify. destruct m0; ss. des_ifs_safe.
      repeat rewrite andb_true_iff in Heq11. des. destruct q; ss.
      assert (n = 3%nat) by (clear - Heq15; des_ifs). subst.
      (* 2 *)
      destruct l; clarify. destruct m0; ss. des_ifs_safe.
      repeat rewrite andb_true_iff in Heq14. des. destruct q; ss.
      assert (n = 2%nat) by (clear - Heq18; des_ifs). subst.
      (* 1 *)
      destruct l; clarify. destruct m0; ss. des_ifs_safe.
      repeat rewrite andb_true_iff in Heq17. des. destruct q; ss.
      assert (n = 1%nat) by (clear - Heq21; des_ifs). subst.
      (* 0 *)
      destruct l; clarify. destruct m0; ss. des_ifs_safe.
      repeat rewrite andb_true_iff in Heq20. des. destruct q; ss.
      assert (n = 0%nat) by (clear - Heq24; des_ifs). subst.
      des_ifs_safe.
      InvBooleans. clarify. clarify.
      inv BIND. inv H4; ss. unfold Mptr in *. des_ifs_safe.
      inv H6. inv H4; ss. unfold Mptr in *. des_ifs_safe.
      rewrite Heq5 in Heq. clarify.
      inv H8. inv H4; ss. unfold Mptr in *. des_ifs_safe.
      rewrite Heq5 in Heq. clarify.
      inv H10. inv H4; ss. unfold Mptr in *. des_ifs_safe.
      rewrite Heq5 in Heq. clarify.
      inv H11. inv H4; ss. unfold Mptr in *. des_ifs_safe.
      rewrite Heq5 in Heq. clarify.
      inv H12. inv H4; ss. unfold Mptr in *. des_ifs_safe.
      rewrite Heq5 in Heq. clarify.
      inv H13. inv H4; ss. unfold Mptr in *. des_ifs_safe.
      rewrite Heq5 in Heq. clarify.
      inv H14. inv H4; ss. unfold Mptr in *. des_ifs_safe.
      rewrite Heq5 in Heq. clarify.
      inv H15. ss. clarify. unfold rev_if_be_mv in *. des_ifs.
      assert (l0 = []); subst.
      { destruct l0; ss. }
      assert (rev (rev (inj_bytes (encode_int 8 (Int64.unsigned (Int64.repr z))))) =
                rev [Byte bt6; Byte bt5; Byte bt4; Byte bt3; Byte bt2; Byte bt1; Byte bt0; Byte bt]).
      { rewrite Heq5. ss. }
      clear Heq5. rewrite rev_involutive in H2. ss. unfold inj_bytes in H2.
      replace [Byte bt; Byte bt0; Byte bt1; Byte bt2; Byte bt3; Byte bt4; Byte bt5; Byte bt6] with
        (map Byte [bt; bt0; bt1; bt2; bt3; bt4; bt5; bt6]) in H2 by ss.
      symmetry. eapply remove_inj_byte; eauto. }
    subst. erewrite decode_encode_int_8; eauto.
Qed.

Lemma load_result_binded chunk m v1 v2
    (BIND: val_intptr m v1 v2):
  <<BIND: val_intptr m (Val.load_result chunk v1) (Val.load_result chunk v2)>>.
Proof.
  inv BIND; destruct chunk; ss; try by econs.
Qed.

(* move *)
Lemma proj_bytes_Some_bytes vl bl
    (BYTES: proj_bytes vl = Some bl):
  <<BYTES: forallb is_byte_mv vl = true>>.
Proof. ginduction vl; ss; i. des_ifs; ss. erewrite IHvl; eauto. Qed.

(* move *)
Lemma check_value_binded
    m vl vl'
    (BIND: list_forall2 (memval_intptr m) vl vl')
    (PTR1: forallb is_ptr_mv vl = true)
    (PTR2: forallb is_ptr_mv vl' = true)
    v v' q n
    (CHECK: check_value n v q vl = true)
    (BINDV: val_intptr m v v') (PTR: exists b' ofs', v' = Vptr b' ofs'):
  <<CHECK: check_value n v' q vl' = true>>.
Proof.
  ginduction BIND; i; destruct n; simpl in *; auto.
  inv H; auto.
  InvBooleans. assert (n = n0) by (apply beq_nat_true; auto). subst v1 q0 n0.
  replace v2 with v'.
  { unfold proj_sumbool; rewrite ! dec_eq_true. rewrite <- beq_nat_refl. simpl; eauto. }
  des. inv BINDV; try discriminate; inv H0; ss.
Qed.

Lemma proj_value_inject:
  forall f q vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  Val.inject f (proj_value q vl1) (proj_value q vl2).
Proof.
  intros. unfold proj_value.
  inversion H; subst. auto. inversion H0; subst; auto.
  destruct (check_value (size_quantity_nat q) v1 q (Fragment v1 q0 n :: al)) eqn:B; auto.
  destruct (Val.eq v1 Vundef). subst; auto.
  erewrite check_value_inject by eauto. auto.
Qed.

(* Lemma check_value_binded_no_ptrlike *)
(*     m vl1 vl2 n v1 v2 q  *)
(*     (NPTRL1: forallb Mem.is_ptrlike_mv vl1 = false) *)
(*     (BIND: list_forall2 (memval_intptr m) vl1 vl2) *)
(*     (CHECK: check_value n v1 q vl1 = true) *)
(*     (BINDV: val_intptr m v1 v2) *)
(*     (UNDEF: v1 <> Vundef) : *)
(*   <<CHECK: check_value n v2 q vl2 = true>>. *)
(* Proof. *)
(*   ginduction BIND; ss. i. destruct n; ss. inv H; ss. *)
(*   { eapply andb_false_iff in NPTRL1. des; ss. InvBooleans; subst. *)
(*     eapply check_value_is_ptr in H2. exfalso. eapply forallb_false_forall in NPTRL1. *)
(*     eapply NPTRL1. ii. eapply forallb_forall in H2; eauto. unfold Mem.is_ptrlike_mv. rewrite H2. *)
(*     rewrite orb_true_r. ss. } *)
(*   2:{ InvBooleans; subst. clarify. } *)
(*   InvBooleans. des; subst. des_ifs_safe. *)
(*   assert (v2 = v3). *)
(*   { inv BINDV; try discriminate; inv H0; auto; ss. *)
(*     3:{ des_ifs. } *)
(*     (* this lemma is not true. because Q32 Vptr is not ptrlike but it can have binded long with Q32. *)
(*        Q32 Vptr will be Vundef by Val.load_result function. not proj_value level -> Q64(Q32 at 32bit) needed. *) *)
(* Abort. *)

Lemma check_value_binded_no_ptrlike
    m vl1 vl2 n v1 v2
    (NPTRL1: forallb Mem.is_ptrlike_mv vl1 = false)
    (BIND: list_forall2 (memval_intptr m) vl1 vl2)
    (CHECK: check_value n v1 Q64 vl1 = true)
    (BINDV: val_intptr m v1 v2)
    (UNDEF: v1 <> Vundef) :
  <<CHECK: check_value n v2 Q64 vl2 = true>>.
Proof.
  ginduction BIND; ss. i. destruct n; ss. inv H; ss.
  { eapply andb_false_iff in NPTRL1. des; ss. InvBooleans; subst.
    eapply check_value_is_ptr in H2. exfalso. eapply forallb_false_forall in NPTRL1.
    eapply NPTRL1. ii. eapply forallb_forall in H2; eauto. unfold Mem.is_ptrlike_mv. rewrite H2.
    rewrite orb_true_r. ss. }
  2:{ InvBooleans; subst. clarify. }
  InvBooleans. des; subst. des_ifs_safe.
  assert (v2 = v3).
  { inv BINDV; try discriminate; inv H0; auto; ss.
    3:{ des_ifs. }
    - eapply andb_false_iff in NPTRL1. des; ss.
      exploit check_value_is_ptr; eauto. i. exfalso. eapply forallb_false_forall in NPTRL1.
      eapply NPTRL1. ii. eapply forallb_forall in H; eauto. unfold Mem.is_ptrlike_mv. rewrite H.
      rewrite orb_true_r. ss.
    - eapply andb_false_iff in NPTRL1. des; ss.
      exploit check_value_is_ptr; eauto. i. exfalso. eapply forallb_false_forall in NPTRL1.
      eapply NPTRL1. ii. eapply forallb_forall in H0; eauto. unfold Mem.is_ptrlike_mv. rewrite H0.
      rewrite orb_true_r. ss. }
  subst. r. eapply andb_false_iff in NPTRL1. des.
  - destruct al.
    { destruct n; ss. inv BIND. ss. repeat rewrite andb_true_iff. esplits; eauto.
      unfold proj_sumbool. des_ifs. }
    exploit check_value_not_ptrlike; eauto. i. erewrite IHBIND; eauto.
    2:{ rewrite forallb_false_forall. ii. r in H.
        rewrite forallb_forall in H. ss. exploit H; eauto. i. exploit H2; eauto. i.
        rewrite H5 in H4. ss. }
    repeat rewrite andb_true_iff. esplits; eauto. unfold proj_sumbool. des_ifs.
  - erewrite IHBIND; eauto. repeat rewrite andb_true_iff. esplits; eauto. unfold proj_sumbool. des_ifs.
Qed.

Lemma decode_val_binded_no_ptrlike
    m1 m2 vl1 vl2 chunk
    (CE: concrete_extends m1 m2)
    (LEN: ((Datatypes.length vl1) > 0)%nat)
    (NPTRL1: forallb Mem.is_ptrlike_mv vl1 = false)
    (BIND: list_forall2 (memval_intptr m2) vl1 vl2) :
  <<BIND: val_intptr m2 (decode_val chunk (Mem.normalize_mvs chunk m1 vl1))
                        (decode_val chunk (Mem.normalize_mvs chunk m2 vl2))>>.
Proof.
  assert (CHECK1: Mem.normalize_check chunk vl1 = false).
  { unfold Mem.normalize_check, Mem.is_mixed_mvs. des_ifs. }
  unfold Mem.normalize_mvs. rewrite CHECK1.
  assert (BYTES1: proj_bytes vl1 = None).
  { clear - NPTRL1. ginduction vl1; ss. ii. rewrite andb_false_iff in NPTRL1. des; des_ifs.
    exploit IHvl1; eauto. i. clarify. }
  destruct (classic (In Undef vl1)).
  { assert (decode_val chunk vl1 = Vundef).
    { unfold decode_val. rewrite BYTES1. do 2 (erewrite proj_value_undef; eauto). des_ifs. }
    rewrite H0. econs. }
  destruct (classic (forall q n, ~ In (Fragment Vundef q n) vl1)); cycle 1.
  { assert (decode_val chunk vl1 = Vundef).
    { unfold decode_val. rewrite BYTES1.
      eapply not_all_ex_not in H0. des. eapply not_all_ex_not in H0. des. eapply NNPP in H0.
      do 2 (erewrite Mem.proj_value_undef_frag; eauto). des_ifs. }
    rewrite H1. econs. }
  rename H into UNDEF1. rename H0 into UNDEF2.
  assert (NPTRL2: forallb Mem.is_ptrlike_mv vl2 = false).
  { clear BYTES1 CHECK1. ginduction BIND; ss; i. rewrite andb_false_iff in *. des.
    - left. inv H; ss.
      + inv H0; ss.
        * des_ifs. destruct q; ss.
        * exfalso. eapply UNDEF2; eauto.
      + exfalso. eapply UNDEF2. eauto.
      + exfalso. eapply UNDEF1. eauto.
    - right. exploit IHBIND; eauto.
      { destruct al; ss. lia. }
      ii. eapply UNDEF2. eauto. }
  assert (CHECK2: Mem.normalize_check chunk vl2 = false).
  { unfold Mem.normalize_check, Mem.is_mixed_mvs. des_ifs. }
  rewrite CHECK2.
  assert (BYTES2: proj_bytes vl2 = None).
  { clear - NPTRL2. ginduction vl2; ss. ii. rewrite andb_false_iff in NPTRL2. des; des_ifs.
    exploit IHvl2; eauto. i. clarify. }
  unfold decode_val. rewrite BYTES1, BYTES2.
  assert (BINDV: val_intptr m2 (proj_value Q64 vl1) (proj_value Q64 vl2)).
  { i. unfold proj_value. des_ifs; try by econs.
    - inv BIND. inv H2. econs.
    - inv BIND. inv H2; try by ss.
      2:{ econs. }
      des_ifs. exploit check_value_is_ptr; eauto. i. exfalso.
      clear - NPTRL1 H. eapply andb_false_iff in NPTRL1. des; ss. des_ifs.
      eapply andb_prop in H. des. rewrite forallb_forall in H0.
      eapply forallb_false_forall in NPTRL1. eapply NPTRL1. i. eapply H0 in H1.
      unfold Mem.is_ptrlike_mv. rewrite H1. rewrite orb_true_r. ss.
    - inv BIND. inv H2; eauto. econs.
    - clear CHECK1 CHECK2 BYTES1 BYTES2 LEN.
      exploit check_value_binded_no_ptrlike; try eapply Heq; eauto.
      { inv BIND. inv H2. eauto. exfalso. eapply UNDEF2. ss. eauto. }
      { ii. subst. exfalso. eapply UNDEF2. ss. eauto. }
      i. clarify. }
  des_ifs; try by econs.
  - eapply load_result_binded; eauto.
  - clear BINDV. unfold Val.load_result.
    destruct (proj_value Q32 vl1) eqn:PROJ1; try by econs.
    (* int make lemma *)
    + assert (vl1 = vl2).
      { unfold proj_value in PROJ1. des_ifs. clear -Heq BIND.
        remember (size_quantity_nat Q32) as qn. clear Heqqn.
        remember (Fragment (Vint i) q n :: l) as vl1. clear Heqvl1.
        ginduction BIND; eauto. ii. destruct qn; ss. des_ifs. InvBooleans. subst.
        erewrite IHBIND; eauto. inv H. inv H6. ss. }
      subst. rewrite PROJ1. econs.
    + assert (vl1 = vl2).
      { unfold proj_value in PROJ1. des_ifs. clear -Heq BIND.
        remember (size_quantity_nat Q32) as qn. clear Heqqn.
        remember (Fragment (Vsingle f) q n :: l) as vl1. clear Heqvl1.
        ginduction BIND; eauto. ii. destruct qn; ss. des_ifs. InvBooleans. subst.
        erewrite IHBIND; eauto. inv H. inv H6. ss. }
      subst. rewrite PROJ1. econs.
Qed.

Lemma decode_val_binded
    m1 m2 vl1 vl2 chunk
    (CE: concrete_extends m1 m2)
    (LEN: ((Datatypes.length vl1) > 0)%nat)
    (BIND: list_forall2 (memval_intptr m2) vl1 vl2) :
  <<BIND: val_intptr m2 (decode_val chunk (Mem.normalize_mvs chunk m1 vl1))
                        (decode_val chunk (Mem.normalize_mvs chunk m2 vl2))>>.
Proof.
  destruct (forallb Mem.is_ptrlike_mv vl1) eqn:PTRL; cycle 1.
  { exploit (not_ptrlike_not_normalize chunk); eauto. intros NORM1.
    eapply decode_val_binded_no_ptrlike; eauto. }
  assert (UNDEF1: ~ In Undef vl1).
  { rewrite forallb_forall in PTRL. ii. eapply PTRL in H. ss. }
  assert (UNDEF2: (forall q n, ~ In (Fragment Vundef q n) vl1)).
  { rewrite forallb_forall in PTRL. ii. eapply PTRL in H. ss. }
  destruct Archi.ptr64 eqn:SF; ss.
  destruct (classic (chunk = Mint64 \/ chunk = Many64)).
  2:{ assert (NORM1: Mem.normalize_check chunk vl1 = false).
      { destruct chunk; ss; des; clarify; exfalso; eapply H; auto. }
      assert (NORM2: Mem.normalize_check chunk vl2 = false).
      { destruct chunk; ss; des; clarify; exfalso; eapply H; auto. }
      unfold Mem.normalize_mvs. rewrite NORM1, NORM2.
      destruct (proj_bytes vl1) eqn:BYTES1.
      { exploit proj_bytes_binded; eauto. i. unfold decode_val. rewrite BYTES1, H0.
        des_ifs; econs. }
      (* make lemma *)
      assert (UNDEF: decode_val chunk vl1 = Vundef).
      { unfold decode_val. rewrite BYTES1.
        destruct (classic (chunk = Many32)).
        { subst. destruct vl1; [ss|]. simpl in PTRL. destruct m; try by ss.
          destruct v; try by ss.
          - eapply andb_prop in PTRL. des. unfold Mem.is_ptrlike_mv in PTRL.
            simpl in PTRL. destruct q; ss; des_ifs.
          - eapply andb_prop in PTRL. des. unfold Mem.is_ptrlike_mv in PTRL.
            simpl in PTRL. destruct q; ss; des_ifs. }
        des_ifs; exfalso; eapply H; eauto. }
      rewrite UNDEF. econs. }
  rename H into CHUNK.
  destruct (Mem.normalize_check chunk vl1) eqn:MIXED1.
(* src mix - tgt mix *)
- exploit normalize_check_bind_normalize_check; eauto. intros MIXED2. des_safe.
  destruct (forallb is_byte_mv (Mem.normalize_mvs chunk m1 vl1)) eqn:BYTES1.
  2:{ exploit normalize_fail; try eapply BYTES1; eauto. i. rewrite H. eapply val_intptr_undef. }
  exploit binded_normalize_binded; eauto. instantiate (1:= chunk). i.
  exploit bytes_binded_bytes; eauto. i. des_safe. rewrite H1. unfold decode_val.
  assert (BYTES : exists bl2, proj_bytes (Mem.normalize_mvs chunk m2 vl2) = Some bl2).
  { destruct (proj_bytes (Mem.normalize_mvs chunk m2 vl2)) eqn:A; eauto.
    rewrite Mem.not_bytes_proj_bytes_iff in A; clarify. }
  des_safe. rewrite BYTES. des_ifs; econs.
(* src not mix *)
- assert (PTR1: forallb is_ptr_mv vl1 = true).
  { unfold Mem.normalize_check, Mem.is_mixed_mvs in MIXED1. rewrite PTRL, SF in MIXED1.
    des_ifs; try by (des; clarify); ss.
    - eapply andb_false_iff in MIXED1. des; clarify. ss. rewrite negb_false_iff in MIXED1. ss.
    - eapply andb_false_iff in MIXED1. des; clarify. ss. rewrite negb_false_iff in MIXED1. ss. }
  destruct (Mem.normalize_check chunk vl2) eqn:MIXED2; cycle 1.
  (* src not mix - tgt not mix *)
+ assert (PTR2: forallb is_ptr_mv vl2 = true).
  { unfold Mem.normalize_check, Mem.is_mixed_mvs in MIXED2.
    erewrite ptrlike_binded_ptrlike in MIXED2; eauto. rewrite SF in MIXED2.
    des_ifs; try by (des; clarify); ss.
    - eapply andb_false_iff in MIXED2. des; clarify. ss. rewrite negb_false_iff in MIXED2. ss.
    - eapply andb_false_iff in MIXED2. des; clarify. ss. rewrite negb_false_iff in MIXED2. ss. }
  (* exploit binded_normalize_binded; eauto. instantiate (1:=chunk). i. *)
  unfold Mem.normalize_mvs. rewrite MIXED1, MIXED2.
  assert (BYTES1: proj_bytes vl1 = None).
  { clear - PTR1 LEN. ginduction vl1; ss; i; [lia|]. eapply andb_prop in PTR1. des. des_ifs; ss. }
  assert (BYTES2: proj_bytes vl2 = None).
  { erewrite list_forall2_length in LEN; eauto.
    clear - PTR2 LEN. ginduction vl2; ss; i; [lia|]. eapply andb_prop in PTR2. des. des_ifs; ss. }
  unfold decode_val. rewrite BYTES1, BYTES2. des; subst. des_ifs_safe.
  * eapply load_result_binded.
    ss. unfold proj_value. inv BIND. ss. inversion H; subst; try by ss.
    destruct (check_value (size_quantity_nat Q64) v1 Q64 (Fragment v1 q n :: al)) eqn:B; try by econs.
    destruct (Val.eq v1 Vundef). subst; econs.
    exploit check_value_binded; try eapply B; eauto.
    { econs; eauto. }
    { simpl in PTR2. des_ifs. esplits; eauto. }
    i. rewrite H2. eauto.
  * ss. unfold proj_value. inv BIND. ss. inversion H; subst; try by ss.
    destruct (check_value (size_quantity_nat Q64) v1 Q64 (Fragment v1 q n :: al)) eqn:B; try by econs.
    destruct (Val.eq v1 Vundef). subst; econs.
    exploit check_value_binded; try eapply B; eauto.
    { econs; eauto. }
    { simpl in PTR2. des_ifs. esplits; eauto. }
    i. rewrite H2. eauto.
  (* src not mix - tgt mix *)
+ exploit binded_normalize_binded; eauto. instantiate (1:=chunk). intros BIND'.
  unfold Mem.normalize_mvs in *. rewrite MIXED1, MIXED2 in *.
  destruct (classic (decode_val chunk vl1 = Vundef)).
  { rewrite H. econs. }
  rename H into NOUNDEF.
  assert (BYTE: forallb is_byte_mv (map (Mem._decode_normalize_mv m2) vl2) = true).
  { assert (BYTES: proj_bytes vl1 = None).
    { clear - PTR1 LEN. ginduction vl1; ss; i; [lia|]. des_ifs; ss. }
    unfold decode_val in NOUNDEF. rewrite BYTES in NOUNDEF. des_ifs.
    - ss. des_ifs.
      { destruct vl1; try by ss. destruct m; try by ss. destruct v; try by ss.
        unfold proj_value in Heq. des_ifs. }
      unfold proj_value in Heq. des_ifs.
      (* make lemma *)
      assert (ALLPTR: forall mv, In mv (Fragment (Vptr b i) q n :: l) -> exists q n, mv = Fragment (Vptr b i) q n).
      { clear - Heq0. remember (size_quantity_nat Q64) as qn. clear Heqqn.
        remember (Fragment (Vptr b i) q n :: l) as ll. clear Heqll.        
        ginduction qn; ss; i.
        { des_ifs. }
        des_ifs. repeat rewrite andb_true_iff in Heq0. des.
        ss. des.
        { unfold proj_sumbool in Heq0. des_ifs. eauto. }
        exploit IHqn; eauto. }
      assert (CONC: exists caddr, m2.(Mem.mem_concrete) ! b = Some caddr).
      { unfold Mem.is_mixed_mvs in MIXED2. repeat rewrite andb_true_iff in MIXED2. des_safe.
        rewrite negb_true_iff in MIXED3.
        assert (existsb (fun mv => Mem.is_intptr_mv mv || is_byte_mv mv) vl2 = true).
        { clear - MIXED0 MIXED3. ginduction vl2; ss; ii. eapply andb_prop in MIXED0. des.
          rewrite andb_false_iff in MIXED3. des.
          - unfold Mem.is_ptrlike_mv in MIXED0. repeat rewrite orb_true_iff in MIXED0. des; clarify.
            rewrite orb_true_r. rewrite orb_true_l. ss.
          - exploit IHvl2; eauto. i. rewrite H. rewrite orb_true_r. ss. }
        rewrite existsb_exists in H. des. exploit list_forall2_in_right; try eapply BIND; eauto. i.
        des. exploit ALLPTR; eauto. i. des. subst. inv H2.
        - simpl in H9. unfold Mem.ptr2int in H9. des_ifs. eauto.
        - ss.
        - inv H7; try by ss. simpl in H6. unfold Mem.ptr2int in H6. des_ifs. eauto. }
      remember (Fragment (Vptr b i) q n :: l) as ll. clear Heqll.
      remember (size_quantity_nat Q64) as qn.
      assert (QQ: (qn <= 8)%nat).
      { clear - Heqqn. subst. unfold size_quantity_nat. lia. }
      clear Heqqn. clear - QQ Heq0 BIND' CONC.
      (* eapply andb_prop in MIXED2. des_safe. *)
      remember (map (Mem._decode_normalize_mv m2) vl2) as ll'.
      ginduction qn; ss.
      { ii. des_ifs. inv BIND'. ss. }
      ii. des_ifs. des. destruct vl2; ss.
      repeat rewrite andb_true_iff in Heq0. des.
      eapply proj_sumbool_true in Heq0. subst. inv BIND'. dup H2. inv H2; ss.
      2:{ rewrite <- H6 in *. inv H0. inv H2; ss.
          - destruct m; ss. unfold Mem.to_int in H6. des_ifs; ss.
            + specialize (inj_bytes_all_bytes (encode_int 4 (Int.unsigned i0))). i.
              eapply nth_error_In in Heq0. unfold rev_if_be_mv in *. des_ifs. ss.
              r in H. rewrite <- in_rev in Heq0. rewrite forallb_forall in H. eapply H in Heq0. ss.
            + specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned i0))). i.
              eapply nth_error_In in Heq0. unfold rev_if_be_mv in *. des_ifs. ss.
              r in H. rewrite <- in_rev in Heq0. rewrite forallb_forall in H. eapply H in Heq0. ss.
            + des_ifs; ss.
              specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned (Int64.repr z)))). i.
              eapply nth_error_In in Heq0. unfold rev_if_be_mv in *. des_ifs. ss.
              r in H. rewrite <- in_rev in Heq0. rewrite forallb_forall in H. eapply H in Heq0. ss.
            + des_ifs. ss. eapply beq_nat_true in Heq2. subst.
              erewrite nth_error_None in Heq0. unfold rev_if_be_mv in Heq0. des_ifs.
              rewrite rev_length in Heq0. erewrite length_inj_bytes, encode_int_length in Heq0. lia.
            + des_ifs. unfold Mem.ptr2int in Heq0. rewrite CONC in Heq0. clarify.
          - unfold Mem.ptr2int in H7. rewrite CONC in H7. des_ifs. ss.
            unfold Mem._decode_normalize_mv in H6. des_ifs.
            + destruct v; ss; clarify; ss.
              * specialize (inj_bytes_all_bytes (encode_int 4 (Int.unsigned i0))). i.
                eapply nth_error_In in Heq0. unfold rev_if_be_mv in *. des_ifs. ss.
                r in H. rewrite <- in_rev in Heq0. rewrite forallb_forall in H. eapply H in Heq0. ss.
              * specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned i0))). i.
                eapply nth_error_In in Heq0. unfold rev_if_be_mv in *. des_ifs. ss.
                r in H. rewrite <- in_rev in Heq0. rewrite forallb_forall in H. eapply H in Heq0. ss.
              * des_ifs. ss.
                specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned (Int64.repr z)))). i.
                eapply nth_error_In in Heq0. unfold rev_if_be_mv in *. des_ifs. ss.
                r in H. rewrite <- in_rev in Heq0. rewrite forallb_forall in H. eapply H in Heq0. ss.
            + ss. clarify. ss. eapply beq_nat_true in Heq2. subst.
              erewrite nth_error_None in Heq0. unfold rev_if_be_mv in Heq0. des_ifs.
              rewrite rev_length in Heq0. erewrite length_inj_bytes, encode_int_length in Heq0. lia. }
      des_ifs_safe. erewrite IHqn; try eapply Heq1; eauto. lia.
    - ss. des_ifs.
      unfold proj_value in NOUNDEF. des_ifs. simpl in PTR1. des_ifs.
      (* make lemma *)
      assert (ALLPTR: forall mv, In mv (Fragment (Vptr b i) q n :: l) -> exists q n, mv = Fragment (Vptr b i) q n).
      { clear - Heq. remember (size_quantity_nat Q64) as qn. clear Heqqn.
        remember (Fragment (Vptr b i) q n :: l) as ll. clear Heqll. 
        ginduction qn; ss; i.
        { des_ifs. }
        des_ifs. repeat rewrite andb_true_iff in Heq. des.
        ss. des.
        { unfold proj_sumbool in Heq. des_ifs. eauto. }
        exploit IHqn; eauto. }
      assert (CONC: exists caddr, m2.(Mem.mem_concrete) ! b = Some caddr).
      { unfold Mem.is_mixed_mvs in MIXED2. repeat rewrite andb_true_iff in MIXED2. des_safe.
        rewrite negb_true_iff in MIXED3.
        assert (existsb (fun mv => Mem.is_intptr_mv mv || is_byte_mv mv) vl2 = true).
        { clear - MIXED0 MIXED3. ginduction vl2; ss; ii. eapply andb_prop in MIXED0. des.
          rewrite andb_false_iff in MIXED3. des.
          - unfold Mem.is_ptrlike_mv in MIXED0. repeat rewrite orb_true_iff in MIXED0. des; clarify.
            rewrite orb_true_r. rewrite orb_true_l. ss.
          - exploit IHvl2; eauto. i. rewrite H. rewrite orb_true_r. ss. }
        rewrite existsb_exists in H. des. exploit list_forall2_in_right; try eapply BIND; eauto. i.
        des. exploit ALLPTR; eauto. i. des. subst. inv H2.
        - simpl in H9. unfold Mem.ptr2int in H9. des_ifs. eauto.
        - ss.
        - inv H7; try by ss. simpl in H6. unfold Mem.ptr2int in H6. des_ifs. eauto. }
      remember (Fragment (Vptr b i) q n :: l) as ll. clear Heqll.
      remember (size_quantity_nat Q64) as qn.
      assert (QQ: (qn <= 8)%nat).
      { clear - Heqqn. subst. unfold size_quantity_nat. lia. }
      clear Heqqn. clear - QQ Heq BIND' CONC.
      (* eapply andb_prop in MIXED2. des_safe. *)
      remember (map (Mem._decode_normalize_mv m2) vl2) as ll'.
      ginduction qn; ss.
      { ii. des_ifs. inv BIND'. ss. }
      ii. des_ifs. des. destruct vl2; ss.
      repeat rewrite andb_true_iff in Heq. des.
      eapply proj_sumbool_true in Heq. subst. inv BIND'. dup H2. inv H2; ss.
      2:{ rewrite <- H6 in *. inv H0. inv H2; ss.
          - destruct m; ss. unfold Mem.to_int in H6. des_ifs; ss.
            + specialize (inj_bytes_all_bytes (encode_int 4 (Int.unsigned i0))). i.
              eapply nth_error_In in Heq3. unfold rev_if_be_mv in *. des_ifs. ss.
              r in H. rewrite <- in_rev in Heq3. rewrite forallb_forall in H. eapply H in Heq3. ss.
            + specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned i0))). i.
              eapply nth_error_In in Heq3. unfold rev_if_be_mv in *. des_ifs. ss.
              r in H. rewrite <- in_rev in Heq3. rewrite forallb_forall in H. eapply H in Heq3. ss.
            + des_ifs; ss.
              specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned (Int64.repr z)))). i.
              eapply nth_error_In in Heq3. unfold rev_if_be_mv in *. des_ifs. ss.
              r in H. rewrite <- in_rev in Heq3. rewrite forallb_forall in H. eapply H in Heq3. ss.
            + des_ifs. ss. eapply beq_nat_true in Heq1. subst.
              erewrite nth_error_None in Heq3. unfold rev_if_be_mv in Heq3. des_ifs.
              rewrite rev_length in Heq3. erewrite length_inj_bytes, encode_int_length in Heq3. lia.
            + des_ifs. unfold Mem.ptr2int in Heq3. rewrite CONC in Heq3. clarify.
          - unfold Mem.ptr2int in H7. rewrite CONC in H7. des_ifs. ss.
            unfold Mem._decode_normalize_mv in H6. des_ifs.
            + destruct v; ss; clarify; ss.
              * specialize (inj_bytes_all_bytes (encode_int 4 (Int.unsigned i0))). i.
                eapply nth_error_In in Heq3. unfold rev_if_be_mv in *. des_ifs. ss.
                r in H. rewrite <- in_rev in Heq3. rewrite forallb_forall in H. eapply H in Heq3. ss.
              * specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned i0))). i.
                eapply nth_error_In in Heq3. unfold rev_if_be_mv in *. des_ifs. ss.
                r in H. rewrite <- in_rev in Heq3. rewrite forallb_forall in H. eapply H in Heq3. ss.
              * des_ifs. ss.
                specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned (Int64.repr z)))). i.
                eapply nth_error_In in Heq3. unfold rev_if_be_mv in *. des_ifs. ss.
                r in H. rewrite <- in_rev in Heq3. rewrite forallb_forall in H. eapply H in Heq3. ss.
            + ss. clarify. ss. eapply beq_nat_true in Heq1. subst.
              erewrite nth_error_None in Heq3. unfold rev_if_be_mv in Heq3. des_ifs.
              rewrite rev_length in Heq3. erewrite length_inj_bytes, encode_int_length in Heq3. lia. }
      des_ifs_safe. erewrite IHqn; try eapply Heq1; eauto. lia. }
  eapply ptr_byte_binded; eauto.
Qed.

Lemma load_concrete_extends chunk m1 m2 b ofs v1
    (CE: concrete_extends m1 m2)
    (LOAD: Mem.load chunk m1 b ofs = Some v1):
  exists v2, <<LOAD: Mem.load chunk m2 b ofs = Some v2>> /\ <<BIND: val_intptr m2 v1 v2>>.
Proof.
  Local Transparent Mem.load. unfold Mem.load in *. des_ifs_safe.
  exploit valid_access_concrete_extends; eauto. i. des_ifs_safe. esplits; eauto.
  eapply decode_val_binded; eauto.
  { rewrite Mem.getN_length. unfold size_chunk_nat. destruct chunk; ss; lia. }
  eapply getN_concrete_extends; eauto.
  rewrite <- size_chunk_conv. inv v. auto.
Qed.

Lemma loadv_concrete_extends chunk m1 m2 addr1 addr2 v1
      (CEXT: concrete_extends m1 m2)
      (LDV: Mem.loadv chunk m1 addr1 = Some v1)
      (BIND: val_intptr m2 addr1 addr2):
  exists v2, Mem.loadv chunk m2 addr2 = Some v2 /\ val_intptr m2 v1 v2.
Proof.
  i. Local Transparent Mem.loadv. unfold Mem.loadv in LDV. destruct addr1; ss; des_ifs.
  - inv BIND. exploit denormalize_concrete_extends; eauto. i. des.
    unfold Mem.loadv. ss. des_ifs. eapply load_concrete_extends; eauto.
  - inv BIND; ss.
    + ss. eapply load_concrete_extends; eauto.
    + unfold Mem.loadv. ss. des_ifs_safe. exploit Mem.load_valid_access; eauto. i. inv H.
      r in H0. specialize (H0 (Ptrofs.unsigned i)). exploit H0.
      { destruct chunk; ss; lia. }
      i. eapply Mem.perm_implies in H.
      2:{ eapply perm_any_N. }
      rewrite <- Mem.valid_pointer_nonempty_perm in H.
      exploit Mem.ptr2int_to_denormalize; eauto.
      { eapply Ptrofs.unsigned_range_2. }
      { rewrite Mem.valid_pointer_nonempty_perm in *. eapply concrete_extends_perm_implies; eauto. }
      i. exploit Mem.denormalize_info; eauto. i. des. rewrite Int64.unsigned_repr; cycle 1.
      { unfold Ptrofs.max_unsigned, Int64.max_unsigned in *. rewrite <- Ptrofs.modulus_eq64; eauto. lia. }
      rewrite H3. des_ifs.
      { exfalso. unfold Int64.eq in Heq1. des_ifs. unfold Ptrofs.max_unsigned in CRANGE0.
        rewrite Ptrofs.modulus_eq64 in CRANGE0; eauto. rewrite Int64.unsigned_repr in e; cycle 1.
        { unfold Int64.max_unsigned. lia. }
        rewrite Int64.unsigned_zero in e. subst. lia. }
      eapply load_concrete_extends; eauto.
      erewrite Ptrofs.unsigned_repr; eauto.
Qed.

Lemma bind_memval_list_refl m vl :
  <<MINDL: list_forall2  (memval_intptr m) vl vl>>.
Proof.
  ginduction vl; ii; ss; econs; eauto. eapply memval_intptr_refl. eapply IHvl.
Qed.

Lemma bind_memval_intptr m chunk v1 v2
    (BIND: val_intptr m v1 v2):
  <<BINDMV: list_forall2 (memval_intptr m) (encode_val chunk v1) (encode_val chunk v2)>>.
Proof.
  inv BIND; ss. des_ifs; try by eapply bind_memval_list_refl.
  - des_ifs; try by eapply bind_memval_list_refl.
  - des_ifs; try by eapply bind_memval_list_refl.
  - des_ifs; try by eapply bind_memval_list_refl.
  - des_ifs; try by eapply bind_memval_list_refl.
  - des_ifs; try by eapply bind_memval_list_refl.
    + unfold inj_bytes. unfold encode_int, rev_if_be. des_ifs. ss.
      assert (TOINT: Mem.to_int (Vptr b ofs) m = Some (Vlong (Int64.repr z))).
      { ss. rewrite Heq. ss. }
      repeat (econs; eauto).
    + unfold inj_bytes. unfold encode_int, rev_if_be. des_ifs. ss.
      assert (TOINT: Mem.to_int (Vptr b ofs) m = Some (Vlong (Int64.repr z))).
      { ss. rewrite Heq. ss. }
      repeat (econs; eauto).
    + unfold inj_value. generalize (size_quantity_nat Q64).
      induction n; ss; [econs|].
      econs; eauto. econs; eauto. econs; eauto. simpl. unfold Mem.ptr2int_v. rewrite Heq. ss.
  - unfold encode_val; des_ifs; ss; try by (repeat econs).
Qed.

Lemma store_concrete_extends
    chunk m1 m2 b ofs v1 m1' v2
    (CE: concrete_extends m1 m2)
    (STORE: Mem.store chunk m1 b ofs v1 = Some m1')
    (BIND: val_intptr m2 v1 v2):
  exists m2', <<STORE: Mem.store chunk m2 b ofs v2 = Some m2'>> /\ <<CE: concrete_extends m1' m2'>>.
Proof.
  exploit Mem.store_valid_access_3; eauto. intros VLD1.
  exploit valid_access_concrete_extends; eauto. intros VLD2. des.
  Local Transparent Mem.store. unfold Mem.store in *. des_ifs_safe. esplits; eauto.
  econs; ss.
- eapply same_nextblock; eauto.
- i. unfold Mem.perm in *. ss. eapply extended_access; eauto.
- i. destruct (eq_block b b0); try subst b0.
+ repeat rewrite PMap.gss in *; eauto.
  eapply same_concrete_memval_intptr with (m1:=m2); ss.
  exploit bind_memval_intptr; eauto. instantiate (1:=chunk). i.
  assert (ACC: forall ofs, Mem.perm m1 b ofs Cur Readable -> memval_intptr m2 (ZMap.get ofs (Mem.mem_contents m1) # b)
                                                                        (ZMap.get ofs (Mem.mem_contents m2) # b)).
  { ii. eapply extended_contents; eauto. }
  destruct (classic (ofs <= ofs0 < ofs + size_chunk chunk)).
  2:{ erewrite Mem.setN_outside in *.
      2:{ rewrite encode_val_length. rewrite <- size_chunk_conv. lia. }
      erewrite Mem.setN_outside.
      2:{ rewrite encode_val_length. rewrite <- size_chunk_conv. lia. }
      eapply same_concrete_memval_intptr with (m1:=m2); eauto. }
  assert (ACC': Mem.perm m1 b ofs0 Cur Readable).
  { inv VLD1. r in H2. exploit H2; eauto. }
  clear - H0 ACC ACC'.
  remember (encode_val chunk v1) as vl1. remember (encode_val chunk v2) as vl2.
  remember ((Mem.mem_contents m1) # b) as c1. remember ((Mem.mem_contents m2) # b) as c2.
  clear - H0 ACC ACC'. revert ACC'. revert ofs0. revert ACC. revert c1 c2 ofs. induction H0; ss; i.
  eapply IHlist_forall2; eauto. ii. rewrite ZMap.gsspec at 1. des_ifs.
  { rewrite ZMap.gss; eauto. }
  { rewrite ZMap.gso; eauto. }
+ repeat (rewrite PMap.gso; eauto). eapply same_concrete_memval_intptr with (m1:=m2); eauto.
  eapply extended_contents; eauto.
- eapply extended_concrete; eauto.
Qed.

Theorem storev_concrete_extends
    chunk m1 m2 addr1 v1 m1' addr2 v2
    (CEXT: concrete_extends m1 m2)
    (STRV: Mem.storev chunk m1 addr1 v1 = Some m1')
    (BIND: val_intptr m2 addr1 addr2)
    (BIND': val_intptr m2 v1 v2):
  exists m2', Mem.storev chunk m2 addr2 v2 = Some m2' /\ concrete_extends m1' m2'.
Proof.
  i. Local Transparent Mem.storev. unfold Mem.storev in STRV. des_ifs.
  - inv BIND. exploit denormalize_concrete_extends; eauto. i. des.
    unfold Mem.storev. des_ifs. eapply store_concrete_extends; eauto.
  - inv BIND; ss.
    + ss. eapply store_concrete_extends; eauto.
    + des_ifs_safe. exploit Mem.store_valid_access_3; eauto. i. inv H.
      r in H0. specialize (H0 (Ptrofs.unsigned i)). exploit H0.
      { destruct chunk; ss; lia. }
      i. eapply Mem.perm_implies in H.
      2:{ eapply perm_any_N. }
      rewrite <- Mem.valid_pointer_nonempty_perm in H.
      exploit Mem.ptr2int_to_denormalize; eauto.
      { eapply Ptrofs.unsigned_range_2. }
      { rewrite Mem.valid_pointer_nonempty_perm in *. eapply concrete_extends_perm_implies; eauto. }
      i. exploit Mem.denormalize_info; eauto. i. des. rewrite Int64.unsigned_repr; cycle 1.
      { unfold Ptrofs.max_unsigned, Int64.max_unsigned in *. rewrite <- Ptrofs.modulus_eq64; eauto. lia. }
      rewrite H3. eapply store_concrete_extends; eauto.
Qed.

Lemma free_concrete_extends
    m1 m2 b lo hi m1'
    (CE: concrete_extends m1 m2)
    (FREE: Mem.free m1 b lo hi = Some m1') :
  exists m2', <<FREE: Mem.free m2 b lo hi = Some m2'>> /\ <<CE: concrete_extends m1' m2'>>.
Proof.
  Local Transparent Mem.free.
  assert (RPERM: Mem.range_perm m1 b lo hi Cur Freeable) by (eapply Mem.free_range_perm; eauto).
  dup RPERM. eapply range_perm_concrete_extends in RPERM; eauto. unfold Mem.free in *. des_ifs_safe.
  esplits; eauto. econs.
  - ss. eapply same_nextblock; eauto.
  - unfold Mem.perm. ss. i.
    destruct (peq b b0); cycle 1.
    { erewrite PMap.gso in *; eauto. eapply extended_access; eauto. }
    subst. erewrite PMap.gss in *. des_ifs.
    eapply extended_access; eauto.
  - ii. ss. eapply same_concrete_memval_intptr with (m1:=m2); eauto.
    inv CE. eapply extended_contents0; eauto. unfold Mem.unchecked_free in H. unfold Mem.perm in *. ss.
    destruct (classic (b = b0)); subst.
    2:{ rewrite PMap.gso in H; eauto. }
    rewrite PMap.gss in H.
    destruct (zle lo ofs && zlt ofs hi) eqn: RANGE; ss.
  - ss. eapply extended_concrete; eauto.
Qed.

Lemma alloc_concrete_extends
    m1 m2 b lo hi m1'
    (CE: concrete_extends m1 m2)
    (ALLOC: Mem.alloc m1 lo hi = (m1', b)) :
  exists m2',  <<FREE: Mem.alloc m2 lo hi = (m2', b)>> /\ <<CE: concrete_extends m1' m2'>>.
Proof.
  Local Transparent Mem.alloc. esplits; eauto.
  { unfold Mem.alloc. eauto. f_equal. injection ALLOC. i. subst b. inv CE; eauto. }
  econs; ss; ii.
  - injection ALLOC; i. subst. ss. erewrite same_nextblock; eauto.
  - injection ALLOC; i. subst. ss. unfold Mem.perm in *; ss. erewrite <- same_nextblock; eauto.
    destruct (peq b0 (Mem.nextblock m1)); subst; ss.
    2:{ rewrite PMap.gso in *; eauto. eapply extended_access; eauto. }
    rewrite PMap.gss in *; ss.
  - injection ALLOC; i; subst. ss. inv CE. rewrite same_nextblock0.
    destruct (classic (b0 = Mem.nextblock m2)); subst.
    { do 2 (rewrite PMap.gss; eauto). rewrite ZMap.gi. econs. }
    do 2 (rewrite PMap.gso; eauto).
    unfold Mem.alloc. ss. esplits; eauto.
    esplits; eauto. eapply same_concrete_memval_intptr with (m1:=m2); ss.
    eapply extended_contents0. unfold Mem.perm in *. ss. rewrite PMap.gso in H; eauto.
    rewrite same_nextblock0. ss.
  - inv CE. eapply extended_concrete0. rewrite <- H.
    eapply Mem.concrete_alloc in ALLOC. rewrite ALLOC. eauto.
Qed.

Lemma capture_concrete_extends
  m1 m2 m2' b addr
  (CE: concrete_extends m1 m2)
  (CAPTURE: Mem.capture m2 b addr m2'):
  exists m1', <<CAPSRC: Mem.capture m1 b addr m1'>> /\ <<CE: concrete_extends m1' m2'>>.
Proof.
  inv CAPTURE.
  assert (Mem.valid_block m1 b).
  { unfold Mem.valid_block in *. erewrite same_nextblock; eauto. }
  destruct (m1.(Mem.mem_concrete) ! b) eqn:CONC.
  { exploit extended_concrete; eauto. i.
    exploit PREVADDR; eauto. i. des; subst. esplits.
    { econs; eauto; i; clarify. }
    assert (m2 = m2').
    { inv CE. destruct m2, m2'; ss. eapply Mem.mkmem_ext; eauto. }
    subst. eauto. }
  set (conc_m1' := PTree.set b addr (Mem.mem_concrete m1)).

  assert (SAME: forall blk caddr, PTree.get blk conc_m1' = Some caddr -> PTree.get blk (m2'.(Mem.mem_concrete)) = Some caddr).
  { subst conc_m1'. i. destruct (peq b blk); subst.
    - erewrite PTree.gss in H0; eauto. clarify.
      destruct ((Mem.mem_concrete m2) ! blk) eqn:CONC2.
      { exploit PREVADDR; eauto. i. des; subst. rewrite <- H1. eauto. }
      exploit CAPTURED; eauto. i. rewrite H0. erewrite PTree.gss; eauto.
    - erewrite PTree.gso in H0; eauto.
      destruct ((Mem.mem_concrete m2) ! b) eqn:CONC2.
      { exploit extended_concrete; eauto. i.
        exploit PREVADDR; eauto. i. des; subst. rewrite <- H3. eauto. }
      exploit CAPTURED; eauto. i. rewrite H1. erewrite PTree.gso; eauto.
      eapply extended_concrete; eauto. }
  
  assert (NEXTLOG: forall b, ~Plt b m1.(Mem.nextblock) -> conc_m1' ! b = None).
  { ii. subst conc_m1'. destruct (eq_block b b0); subst.
    - rewrite PTree.gss. exfalso. eapply H0. unfold Mem.valid_block in VALID. eauto.
    - rewrite PTree.gso; eauto. eapply (Mem.nextblocks_logical m1); eauto. }

  assert (VB: forall b addr, Mem.addr_in_block conc_m1' m1.(Mem.mem_access) addr b ->
                        addr < Ptrofs.modulus - 1).
  { ii. eapply m2'.(Mem.valid_address_bounded). rewrite <- ACCESS.
    instantiate (1:=b0). inv H0. des. econs; eauto.
    exploit extended_access; eauto.
    { unfold Mem.perm. erewrite PERM; eauto. ss. econs. }
    i. unfold Mem.perm, Mem.perm_order' in H0. des_ifs; eauto. }

  assert (NC: forall addr, uniqueness (Mem.addr_in_block conc_m1' m1.(Mem.mem_access) addr)).
  { ii.
    specialize (m2'.(Mem.no_concrete_overlap) addr0). i. r in H2. eapply H2.
    { inv H0. des.
      exploit extended_access; eauto.
      { unfold Mem.perm. erewrite PERM; eauto. ss. econs. }
      i. unfold Mem.perm, Mem.perm_order' in H0. des_ifs; eauto.
      econs; eauto. rewrite <- ACCESS; eauto. }
    { inv H1. des.
      exploit extended_access; eauto.
      { unfold Mem.perm. erewrite PERM; eauto. ss. econs. }
      i. unfold Mem.perm, Mem.perm_order' in H1. des_ifs; eauto.
      econs; eauto. rewrite <- ACCESS; eauto. }
  }

  assert (CA: forall b addr, conc_m1' ! b = Some addr ->
                        forall ofs chunk, (forall o, ofs <= o < ofs + size_chunk chunk ->
                                           Mem.perm_order' (m1.(Mem.mem_access) # b o Max) Nonempty) ->
                                           (align_chunk chunk | addr)).
  { i. eapply SAME in H0.
    eapply m2'.(Mem.concrete_align); eauto. i. eapply H1 in H2.
    rewrite <- ACCESS. eapply extended_access; eauto.
  }

  assert (WVR: forall b addr ofs, conc_m1' ! b = Some addr -> 0 <= ofs < Ptrofs.modulus ->
                             Mem._weak_valid_pointer m1.(Mem.mem_access) b ofs Max ->
                             Mem.in_range (addr + ofs) (1, Ptrofs.modulus)).
  { i. eapply SAME in H0.
    eapply m2'.(Mem.weak_valid_address_range); eauto. rewrite <- ACCESS.
    eapply _weak_valid_concrete_extends; eauto. }

  exists (Mem.mkmem m1.(Mem.mem_contents) m1.(Mem.mem_access) conc_m1' m1.(Mem.nextblock)
               m1.(Mem.access_max) m1.(Mem.nextblock_noaccess) m1.(Mem.contents_default)
               NEXTLOG VB NC CA WVR).
  split.
  - econs; eauto; ss. i; clarify.
  - econs; eauto; ss.
    + erewrite same_nextblock; eauto.
    + unfold Mem.perm. ss. erewrite <- ACCESS. eapply extended_access; eauto.
    + i; ss. rewrite <- CONTENTS.
      exploit extended_contents; eauto. ii.
      inv H1; try by econs; eauto.
      * econs; eauto. unfold Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in H5. des_ifs.
        assert ((Mem.mem_concrete m2') ! b1 = Some z0).
        { destruct (eq_block b1 b); subst.
          { exploit PREVADDR; eauto. i. des. rewrite <- H5; eauto. }
          destruct ((Mem.mem_concrete m2) ! b) eqn:CONC2.
          { exploit PREVADDR; eauto. i. des; subst. rewrite <- H5. eauto. }
          exploit CAPTURED; eauto. i. rewrite H1. rewrite PTree.gso; eauto. }
        unfold Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *. rewrite H1. des_ifs.
      * econs; eauto. inv H4; try by econs; eauto. econs; eauto.
        destruct (eq_block b1 b); subst.
        { unfold Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
          destruct ((Mem.mem_concrete m2) ! b) eqn:CONC2.
          { exploit PREVADDR; eauto. i. des. subst. des_ifs_safe. rewrite <- H6, CONC2. eauto. }
          clarify. }
        unfold Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in H5. des_ifs.
        destruct ((Mem.mem_concrete m2) ! b) eqn:CONC2.
        { exploit PREVADDR; eauto. i. des. subst.
          unfold Mem.to_int, Mem.ptr2int_v, Mem.ptr2int. rewrite <- H5. rewrite Heq0. des_ifs. }
        exploit CAPTURED; eauto. i.
        unfold Mem.to_int, Mem.ptr2int_v, Mem.ptr2int. rewrite H4.
        erewrite PTree.gso; eauto. rewrite Heq0. des_ifs.
Qed.

Lemma capture_concrete_extends_backward_progress
    m1 b addr m1' m2
    (CONC: concrete_extends m1 m1')
    (CAPTURE: Mem.capture m1 b addr m2) :
  (exists m2' addr',
      <<CAPTGT: Mem.capture m1' b addr' m2'>>)
    \/ <<OOM: Mem.capture_oom m1' b>>.
Proof.
  inv CAPTURE; inv CONC.
  assert (Mem.valid_block m1' b).
  { unfold Mem.valid_block in *. rewrite <- same_nextblock0. auto. }
  destruct (classic (exists m2' addr', Mem.capture m1' b addr' m2')).
  - des. left; eauto.
  - right. red. split; eauto.
Qed.

Theorem loadbytes_concrete_extends
    m1 m2 b ofs len bytes1
    (CONC: concrete_extends m1 m2)
    (LD: Mem.loadbytes m1 b ofs len = Some bytes1):
  exists bytes2, Mem.loadbytes m2 b ofs len = Some bytes2 /\ list_forall2 (memval_intptr m2) bytes1 bytes2.
Proof.
  Local Transparent Mem.loadbytes.
  unfold Mem.loadbytes in LD.
  destruct (Mem.range_perm_dec m1 b ofs (ofs + len) Cur Readable); inv LD.
  exists (Mem.getN (Z.to_nat len) ofs (m2.(Mem.mem_contents)#b)).
  split.
  - apply pred_dec_true. eapply concrete_extends_range_perm_implies; eauto.
  - eapply getN_concrete_extends; eauto. 
    destruct (zle 0 len). rewrite Z2Nat.id by lia. auto.
    rewrite Z_to_nat_neg by lia. simpl. red; intros; extlia.
Qed.

Theorem storebytes_within_concrete_extends
    m1 m2 b ofs bytes1 m1' bytes2
    (CONC: concrete_extends m1 m2)
    (SB: Mem.storebytes m1 b ofs bytes1 = Some m1')
    (BIND: list_forall2 (memval_intptr m2) bytes1 bytes2):
  exists m2',
    Mem.storebytes m2 b ofs bytes2 = Some m2'
  /\ concrete_extends m1' m2'.
Proof.
  assert (Mem.range_perm m2 b ofs (ofs + Z.of_nat (length bytes2)) Cur Writable).
  { eapply concrete_extends_range_perm_implies; eauto.
    exploit list_forall2_length; eauto. i. erewrite <- H.
    eapply Mem.storebytes_range_perm; eauto. }
  destruct (Mem.range_perm_storebytes _ _ _ _ H) as [n2 STORE].
  exists n2. esplits; eauto. inv CONC. econs.
  - eapply Mem.nextblock_storebytes in SB, STORE. rewrite SB, STORE; eauto.
  - eapply Mem.storebytes_access in SB, STORE. unfold Mem.perm.
    rewrite SB, STORE. eapply extended_access0; eauto.
  - i. assert (Mem.perm m1 b0 ofs0 Cur Readable). eapply Mem.perm_storebytes_2; eauto.
    rewrite (Mem.storebytes_mem_contents _ _ _ _ _ SB).
    rewrite (Mem.storebytes_mem_contents _ _ _ _ _ STORE).
    rewrite ! PMap.gsspec. destruct (peq b0 b).
    + subst b0. apply setN_concrete_extends with (access := fun ofs => Mem.perm m1 b ofs Cur Readable); eauto.
      { eapply same_concrete_memval_intptr_list; try eapply BIND.
        eapply Mem.concrete_storebytes. eauto. }
      i. eapply same_concrete_memval_intptr; try eapply H2.
      eapply Mem.concrete_storebytes. eauto. eapply extended_contents0; eauto.
    + exploit extended_contents0; eauto. i. eapply same_concrete_memval_intptr; try eapply H2.
      eapply Mem.concrete_storebytes. eauto.
  - eapply Mem.concrete_storebytes in SB, STORE. rewrite <- SB, <- STORE. eauto.
Qed.

End MemRel.

Lemma to_int_bind m m' v v'
    (CONCEXT: concrete_extends m m')
    (BIND: val_intptr m' v v') :
  <<BIND': val_intptr m' (to_int_val m v) (to_int_val m' v')>>.
Proof.
  inv BIND; ss; unfold to_int_val; ss; try (by econs).
  - destruct (Mem.ptr2int b (Ptrofs.unsigned ofs) m) eqn:P2I; ss; [|econs].
    exploit ptr2int_conc_ext; eauto. i. destruct (Archi.ptr64) eqn:BIT; rewrite H; econs.
  - des_ifs; ss; try econs. exploit ptr2int_conc_ext; eauto. i. clarify. econs.
Qed.

(** 32bit lemmas *)

Lemma add_bind m2 v1 v2 v1' v2'
  (BIND1: val_intptr m2 v1 v1')
  (BIND2: val_intptr m2 v2 v2') :
  <<BIND: val_intptr m2 (Val.add v1 v2) (Val.add v1' v2')>>.
Proof.
  intros. unfold Val.add. destruct Archi.ptr64 eqn:SF.
- inv BIND1; inv BIND2; econs.
- destruct v1; (try by econs); destruct v2; try by econs.
  + inv BIND1; inv BIND2. eapply val_intptr_refl.
  + inv BIND1; inv BIND2; [| |clarify].
    { eapply val_intptr_refl. }
    { simpl in *. unfold Mem.ptr2int_v, Mem.ptr2int in *.
      destruct ((Mem.mem_concrete m2) ! b) eqn: CONC; [| clarify].
      rewrite SF in *. inv H3. econs; eauto.
      simpl. unfold Mem.ptr2int_v, Mem.ptr2int. rewrite CONC, SF. do 2 f_equal.
      eapply Int.same_if_eq. unfold Int.eq, Ptrofs.to_int, Ptrofs.of_int, Int.add, Ptrofs.add.
      repeat rewrite Int.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
      eapply Ptrofs.modulus_eq32 in SF. rewrite SF.
      repeat rewrite Zplus_mod_idemp_r. rewrite Z.add_assoc.
      replace (z + (Ptrofs.unsigned i0 + Int.unsigned i mod Int.modulus))
        with ((z + Ptrofs.unsigned i0) + Int.unsigned i mod Int.modulus) by lia.
      rewrite Zplus_mod_idemp_r.
      replace (z + Ptrofs.unsigned i0 + Int.unsigned i) with
        (Int.unsigned i + z + Ptrofs.unsigned i0) by lia. des_ifs; eauto. }
  + inv BIND1; inv BIND2; [| |clarify].
    { eapply val_intptr_refl. }
    { simpl in *. unfold Mem.ptr2int_v, Mem.ptr2int in *.
      destruct ((Mem.mem_concrete m2) ! b) eqn: CONC; [| clarify].
      rewrite SF in *. inv H3. econs; eauto.
      simpl in *. unfold Mem.ptr2int_v, Mem.ptr2int. rewrite CONC, SF. do 2 f_equal.
      eapply Int.same_if_eq. unfold Int.eq, Ptrofs.to_int, Ptrofs.of_int, Int.add, Ptrofs.add.
      repeat rewrite Int.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
      eapply Ptrofs.modulus_eq32 in SF. rewrite SF.
      rewrite Zplus_mod_idemp_r. rewrite Zplus_mod_idemp_l.
      replace (z + (Ptrofs.unsigned i + Int.unsigned i0 mod Int.modulus))
        with ((z + Ptrofs.unsigned i) + Int.unsigned i0 mod Int.modulus) by lia.
      rewrite Zplus_mod_idemp_r. des_ifs; lia. }
Qed.

Lemma sub_bind m2 v1 v2 v1' v2'
    (BIND1: val_intptr m2 v1 v1')
    (BIND2: val_intptr m2 v2 v2') :
  <<BIND: val_intptr m2 (Val.sub v1 v2) (Val.sub v1' v2')>>.
Proof.
  intros. unfold Val.sub. destruct Archi.ptr64 eqn:SF.
- inv BIND1; inv BIND2; econs.
- destruct v1; (try by econs); destruct v2; try by econs.
  + inv BIND1; inv BIND2. eapply val_intptr_refl.
  + inv BIND1; inv BIND2; [| |clarify].
    { eapply val_intptr_refl. }
    { simpl in *. unfold Mem.ptr2int_v, Mem.ptr2int in *.
      destruct ((Mem.mem_concrete m2) ! b) eqn: CONC; [|clarify].
      rewrite SF in *. inv H3. econs; eauto.
      simpl. unfold Mem.ptr2int_v, Mem.ptr2int. rewrite CONC, SF. do 2 f_equal.
      eapply Int.same_if_eq. unfold Int.eq, Ptrofs.to_int, Ptrofs.of_int, Int.sub, Ptrofs.sub.
      repeat rewrite Int.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
      eapply Ptrofs.modulus_eq32 in SF. rewrite SF.
      rewrite Zminus_mod_idemp_l. rewrite Zminus_mod_idemp_r. rewrite Zplus_mod_idemp_r.
      rewrite <- Z.add_opp_r. rewrite Z.add_assoc. des_ifs; lia. }
Qed.

Lemma mul_bind m2 v1 v2 v1' v2'
    (BIND1: val_intptr m2 v1 v1')
    (BIND2: val_intptr m2 v2 v2') :
  <<BIND: val_intptr m2 (Val.mul v1 v2) (Val.mul v1' v2')>>.
Proof. inv BIND1; inv BIND2; ss; econs; eauto. Qed.

Lemma addl_bind m2 v1 v2 v1' v2'
    (BIND1: val_intptr m2 v1 v1')
    (BIND2: val_intptr m2 v2 v2') :
  <<BIND: val_intptr m2 (Val.addl v1 v2) (Val.addl v1' v2')>>.
Proof.
  intros. unfold Val.addl. destruct Archi.ptr64 eqn:SF; cycle 1.
- inv BIND1; inv BIND2; econs.
- destruct v1; (try by econs); destruct v2; try by econs.
  + inv BIND1; inv BIND2. eapply val_intptr_refl.
  + inv BIND1; inv BIND2; [|clarify|].
    { eapply val_intptr_refl. }
    { simpl in *. unfold Mem.ptr2int_v, Mem.ptr2int in *.
      destruct ((Mem.mem_concrete m2) ! b) eqn: CONC; [|clarify].
      rewrite SF in *. inv H3. econs; eauto.
      simpl. unfold Mem.ptr2int_v, Mem.ptr2int. rewrite CONC, SF. do 2 f_equal.
      eapply Int64.same_if_eq. unfold Int64.eq, Ptrofs.to_int64, Ptrofs.of_int64, Int64.add, Ptrofs.add.
      repeat rewrite Int64.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
      eapply Ptrofs.modulus_eq64 in SF. rewrite SF.
      repeat rewrite Zplus_mod_idemp_r.
      replace (z + (Ptrofs.unsigned i0 + Int64.unsigned i mod Int64.modulus))
        with ((z + Ptrofs.unsigned i0) + Int64.unsigned i mod Int64.modulus) by lia.
      rewrite Zplus_mod_idemp_r. rewrite Z.add_assoc.
      replace (z + Ptrofs.unsigned i0 + Int64.unsigned i) with
        (Int64.unsigned i + z + Ptrofs.unsigned i0) by lia. des_ifs; eauto. }
  + inv BIND1; inv BIND2; [|clarify|].
    { eapply val_intptr_refl. }
    { simpl in *. unfold Mem.ptr2int_v, Mem.ptr2int in *.
      destruct ((Mem.mem_concrete m2) ! b) eqn: CONC; [|clarify].
      rewrite SF in *. inv H3. econs; eauto.
      simpl. unfold Mem.ptr2int_v, Mem.ptr2int. rewrite CONC, SF. do 2 f_equal.
      eapply Int64.same_if_eq. unfold Int64.eq, Ptrofs.to_int64, Ptrofs.of_int64, Int64.add, Ptrofs.add.
      repeat rewrite Int64.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
      eapply Ptrofs.modulus_eq64 in SF. rewrite SF.
      rewrite Zplus_mod_idemp_r. rewrite Zplus_mod_idemp_l.
      replace (z + (Ptrofs.unsigned i + Int64.unsigned i0 mod Int64.modulus))
        with ((z + Ptrofs.unsigned i) + Int64.unsigned i0 mod Int64.modulus) by lia.
      rewrite Zplus_mod_idemp_r. des_ifs; lia. }
Qed.

Lemma subl_bind m2 v1 v2 v1' v2'
  (BIND1: val_intptr m2 v1 v1')
  (BIND2: val_intptr m2 v2 v2') :
  <<BIND: val_intptr m2 (Val.subl v1 v2) (Val.subl v1' v2')>>.
Proof.
  intros. unfold Val.subl. destruct Archi.ptr64 eqn:SF; cycle 1 .
- inv BIND1; inv BIND2; econs.
- destruct v1; (try by econs); destruct v2; try by econs.
  + inv BIND1; inv BIND2. eapply val_intptr_refl.
  + inv BIND1; inv BIND2; [|clarify|].
    { eapply val_intptr_refl. }
    { simpl in *. unfold Mem.ptr2int_v, Mem.ptr2int in *.
      destruct ((Mem.mem_concrete m2) ! b) eqn: CONC; [|clarify].
      rewrite SF in *. inv H3. econs; eauto.
      simpl. unfold Mem.ptr2int_v, Mem.ptr2int. rewrite CONC, SF. do 2 f_equal.
      eapply Int64.same_if_eq. unfold Int64.eq, Ptrofs.to_int64, Ptrofs.of_int64, Int64.sub, Ptrofs.sub.
      repeat rewrite Int64.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
      eapply Ptrofs.modulus_eq64 in SF. rewrite SF.
      rewrite Zminus_mod_idemp_l. rewrite Zminus_mod_idemp_r. rewrite Zplus_mod_idemp_r.
      rewrite <- Z.add_opp_r. rewrite Z.add_assoc. des_ifs; lia. }
Qed.

Lemma mull_bind m2 v1 v2 v1' v2'
    (BIND1: val_intptr m2 v1 v1')
    (BIND2: val_intptr m2 v2 v2') :
  <<BIND: val_intptr m2 (Val.mull v1 v2) (Val.mull v1' v2')>>.
Proof. inv BIND1; inv BIND2; ss; econs; eauto. Qed.

(* merge IntPtrRef version *)
Lemma normalize_binded m' v v' ty
    (BIND: val_intptr m' v v') :
  <<BIND: val_intptr m' (Val.normalize v ty) (Val.normalize v' ty)>>.
Proof.
  intros. inv BIND.
- destruct ty; constructor.
- destruct ty; constructor.
- destruct ty; constructor.
- destruct ty; constructor.
- simpl. destruct ty.
+ destruct Archi.ptr64; econstructor; eauto.
+ econs.
+ destruct Archi.ptr64; econstructor; eauto.
+ econs.
+ destruct Archi.ptr64; econstructor; eauto.
+ econstructor; eauto.
- destruct ty; unfold Val.normalize.
  { rewrite H. econs; eauto. }
  { econs. }
  { rewrite H. econs. }
  { econs. }
  { rewrite H. econs; eauto. }
  { econs; eauto. }
- destruct ty; try (by ss).
  { ss. rewrite H. econs. }
  { ss. econs. }
  { ss. rewrite H. econs; eauto. }
  { ss. econs. }
  { ss. rewrite H. econs. }
  { ss. econs; eauto. }
- constructor.
Qed.

Section MEMCONC.

Definition memory_block_concretize (m m': mem) : Prop :=
    m.(Mem.mem_contents) = m'.(Mem.mem_contents)
  /\ m.(Mem.mem_access) = m'.(Mem.mem_access)
  /\ m.(Mem.nextblock) = m'.(Mem.nextblock)
  /\ (forall b addr, m.(Mem.mem_concrete) ! b = Some addr -> m'.(Mem.mem_concrete) ! b = Some addr)
  /\ (forall b (VLD: Mem.valid_block m b), exists addr, m'.(Mem.mem_concrete) ! b = Some addr).

Definition valid_pointer_frag (q: quantity) (n: nat) : bool :=
  if Archi.ptr64 then (quantity_eq q Q64) && (Nat.ltb n 8) else (quantity_eq q Q32) && (Nat.ltb n 4).

Definition memval_intptr_lbd (m: mem) (mv mv': memval) : Prop :=
  match mv with
  | Fragment (Vptr b ofs) q n =>
      if (valid_pointer_frag q n) && (Mem.is_valid m b)
      then memval_intptr m mv mv' /\ (is_byte_mv mv')
      (* invalid fragment. CompCert can't read or concretize this *)
      else mv = mv' 
  | Fragment Vundef _ _ => (* mv' = Byte Byte.zero *) mv = mv'
  | Undef => (* mv' = Byte Byte.zero *) mv = mv'
  | _ => memval_intptr m mv mv'
  end.

Definition memval_intptr_lbd_func (m: mem) (mv: memval) : memval :=
  match mv with
  | Fragment (Vptr b ofs) q n =>
      if (valid_pointer_frag q n) && (Mem.is_valid m b)
      then (match Mem.to_int (Vptr b ofs) m with
            | Some v => match (nth_error (rev_if_be_mv (encode_val Mptr v)) n) with
                       | Some bt => bt
                       | _ => Undef
                       end
            | _ => Undef
            end)        
      (* invalid fragment. CompCert can't read or concretize this *)
      else mv
  (* undef fragment *)
  | Fragment Vundef _ _ => mv
  (* undef fragment *)
  | Undef => mv
  | _ => mv
  end.

Definition memory_concretize_contents (m m': mem) : Prop :=
    m.(Mem.mem_access) = m'.(Mem.mem_access)
  /\ m.(Mem.nextblock) = m'.(Mem.nextblock)
  /\ m.(Mem.mem_concrete) = m'.(Mem.mem_concrete)
  /\ forall b ofs,
      memval_intptr_lbd m' (ZMap.get ofs (m.(Mem.mem_contents) # b)) (ZMap.get ofs (m'.(Mem.mem_contents) # b)).

Lemma memval_intptr_lbd_success m mv
    (ALLCONC: forall b (VLD: Mem.valid_block m b), exists addr, m.(Mem.mem_concrete) ! b = Some addr):
  exists mv', memval_intptr_lbd m mv mv'.
Proof.
  destruct mv; ss; try by (esplits; eauto).
  { eexists. econs. }
  destruct v; try by (esplits; eauto; try eapply memval_intptr_refl). des_ifs.
  2:{ esplits; eauto. }
  eapply andb_prop in Heq. des.
  exploit (ALLCONC b).
  { rewrite Mem.valid_block_iff_is_valid. eauto. }
  i. des.
  unfold valid_pointer_frag in Heq. des_ifs. eapply andb_prop in Heq. des.
  destruct q; ss.
  assert (exists v, Mem.to_int (Vptr b i) m = Some v).
  { ss. unfold Mem.ptr2int. rewrite H. esplits; eauto. }
  des.
  assert (exists bt, nth_error (rev_if_be_mv (encode_val Mptr v)) n = Some bt).
  { destruct (nth_error (rev_if_be_mv (encode_val Mptr v)) n) eqn:NTH; eauto.
    exfalso. 
    simpl in H0. des_ifs. unfold Mem.ptr2int in Heq3. des_ifs. ss.
    unfold Mptr. des_ifs. unfold rev_if_be_mv in *; des_ifs.
    rewrite nth_error_None in NTH. rewrite rev_length in NTH.
    rewrite length_inj_bytes in NTH. rewrite encode_int_length in NTH.
    rewrite Nat.ltb_lt in Heq2. lia. }
  des.
  assert (exists b, bt = Byte b).
  { simpl in H0. des_ifs. unfold Mem.ptr2int in Heq3. des_ifs. ss.
    unfold Mptr. des_ifs. unfold rev_if_be_mv in *; des_ifs.
    eapply nth_error_In in H1. rewrite <- in_rev in H1.
    specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned (Int64.repr (addr + Ptrofs.unsigned i))))).
    i. des. rewrite forallb_forall in H. eapply H in H1. destruct bt; ss; eauto. }
  des. subst. dup H0.
  simpl in H0. des_ifs. unfold Mem.ptr2int in Heq3. des_ifs.
  esplits; [econs; eauto| ss].
Qed.

Lemma memval_intptr_lbd_determ m mv mv1 mv2
    (MVL1: memval_intptr_lbd m mv mv1)
    (MVL2: memval_intptr_lbd m mv mv2):
  mv1 = mv2.
Proof.
  unfold memval_intptr_lbd in *. des_ifs; inv MVL1; inv MVL2; ss; eauto.
  { inv H3; inv H4; eauto. }
  { inv H3; inv H4; eauto. }
  { inv H3; inv H4; eauto. }
  { inv H3; inv H4; eauto. }
  inv H; inv H1; ss. des_ifs.
Qed.

Lemma memval_intptr_lbd_same_func m mv
    (ALLCONC: forall b (VLD: Mem.valid_block m b), exists addr, m.(Mem.mem_concrete) ! b = Some addr):
  memval_intptr_lbd m mv (memval_intptr_lbd_func m mv).
Proof.
  unfold memval_intptr_lbd_func. des_ifs; try by (repeat econs).
  - dup Heq0. dup Heq1. unfold Mem.to_int in Heq2. simpl in Heq2. des_ifs.
    unfold Mem.ptr2int in Heq4. des_ifs. unfold Mptr in Heq3. des_ifs.
    destruct q; try by ss. unfold rev_if_be_mv in Heq3. des_ifs.
    exploit nth_error_In; eauto. i. simpl in H. rewrite <- in_rev in H.
    specialize (inj_bytes_all_bytes (encode_int 8 (Int64.unsigned (Int64.repr (z0 + Ptrofs.unsigned i))))).
    i. des. rewrite forallb_forall in H0. exploit H0; eauto. i. destruct m0; ss.
    rewrite Heq. esplits; eauto. econs; eauto.
  - exfalso. eapply nth_error_None in Heq1. ss. des_ifs.
    unfold Mem.ptr2int, Mptr, rev_if_be_mv in *. des_ifs.
    rewrite rev_length in Heq1. ss. erewrite length_inj_bytes in Heq1. erewrite encode_int_length in Heq1.
    eapply andb_prop in Heq. unfold valid_pointer_frag in Heq. des. des_ifs. eapply andb_prop in Heq. des.
    rewrite Nat.ltb_lt in Heq5. lia.
  - exfalso. eapply andb_prop in Heq. des. erewrite <- Mem.valid_block_iff_is_valid in Heq1.
    exploit ALLCONC; eauto. i. des. ss. unfold Mem.ptr2int in *. des_ifs.
  - r. rewrite Heq. eauto.
Qed.

Lemma lbd_contents_success
    (cont: PMap.t (ZMap.t memval)) m
    (ALLCONC: forall b (VLD: Mem.valid_block m b), exists addr, m.(Mem.mem_concrete) ! b = Some addr):
  exists cont', forall b ofs, memval_intptr_lbd m (ZMap.get ofs (PMap.get b cont)) (ZMap.get ofs cont' !! b).
Proof.
  remember (ZMap.map (memval_intptr_lbd_func m)) as zm.
  remember (PMap.map zm) as pm.
  exists (pm cont). subst. i. rewrite PMap.gmap. rewrite ZMap.gmap.
  eapply memval_intptr_lbd_same_func; eauto.
Qed.

Lemma same_concrete_memval_intptr_lbd
    m1 m2 mv1 mv2
    (SAMENXT: Mem.nextblock m1 = Mem.nextblock m2)
    (SAME: Mem.mem_concrete m1 = Mem.mem_concrete m2)
    (LBD: memval_intptr_lbd m1 mv1 mv2):
  memval_intptr_lbd m2 mv1 mv2.
Proof.
  unfold memval_intptr_lbd in *. des_ifs; try by eapply same_concrete_memval_intptr; eauto.
  - des. esplit; eauto. eapply same_concrete_memval_intptr; eauto.
  - eapply andb_prop in Heq. des. rewrite Heq in Heq0. ss.
    exfalso. unfold Mem.is_valid in *. rewrite SAMENXT in Heq0. clarify.
  - eapply andb_prop in Heq0. des. rewrite Heq0 in Heq. ss.
    exfalso. unfold Mem.is_valid in *. rewrite SAMENXT in Heq1. clarify.
Qed.

Lemma memory_concretize_contents_exists_aux m
    (ALLCONC: forall b (VLD: Mem.valid_block m b), exists addr, m.(Mem.mem_concrete) ! b = Some addr):
  exists m', memory_concretize_contents m m'.
Proof.
  remember (PMap.map (ZMap.map (memval_intptr_lbd_func m)) m.(Mem.mem_contents)) as cont'.

  assert (AM : forall b ofs, Mem.perm_order'' (m.(Mem.mem_access) !! b ofs Max) (m.(Mem.mem_access) !! b ofs Cur)).
  { eapply Mem.access_max. }
  
  assert (NBD: forall b ofs k, ~ Plt b m.(Mem.nextblock) -> m.(Mem.mem_access) !! b ofs k = None).
  { eapply Mem.nextblock_noaccess. }
  
  assert (CD: forall b, fst cont' !! b = Undef).
  { subst. i. specialize (Mem.contents_default m b). i.
    destruct ((Mem.mem_contents m) !! b) eqn:A. ss. subst.
    rewrite PMap.gmap. rewrite A. ss. }

  assert (NL: forall b, ~ Plt b m.(Mem.nextblock) -> m.(Mem.mem_concrete) ! b = None).
  { eapply Mem.nextblocks_logical. }

  assert (VAB: forall bo addr,
             Mem.addr_in_block m.(Mem.mem_concrete) m.(Mem.mem_access) addr bo -> addr < Ptrofs.modulus - 1).
  { eapply Mem.valid_address_bounded. }

  assert (NCO: forall addr, uniqueness (Mem.addr_in_block m.(Mem.mem_concrete) m.(Mem.mem_access) addr)).
  { eapply Mem.no_concrete_overlap. }
  
  assert (CA:  forall (b : positive) (zero_addr : Z),
             m.(Mem.mem_concrete) ! b = Some zero_addr ->
             forall (ofs : Z) (chunk : memory_chunk),
               (forall o : Z, ofs <= o < ofs + size_chunk chunk -> Mem.perm_order' (m.(Mem.mem_access) !! b o Max) Nonempty) ->
               (align_chunk chunk | zero_addr)).
  { eapply Mem.concrete_align. }
  
  assert (WVAR: forall b zero_addr ofs,
             m.(Mem.mem_concrete) ! b = Some zero_addr ->
             0 <= ofs < Ptrofs.modulus ->
             Mem._weak_valid_pointer m.(Mem.mem_access) b ofs Max -> Mem.in_range (zero_addr + ofs) (1, Ptrofs.modulus)).
  { eapply Mem.weak_valid_address_range. }

  exists (Mem.mkmem cont' m.(Mem.mem_access) m.(Mem.mem_concrete) m.(Mem.nextblock) AM NBD CD NL VAB NCO CA WVAR).
  econs; ss; esplits; eauto.
  i. eapply same_concrete_memval_intptr_lbd; simpl; eauto.
  subst. rewrite PMap.gmap. rewrite ZMap.gmap.
  eapply memval_intptr_lbd_same_func; eauto.
Qed.

End MEMCONC.
