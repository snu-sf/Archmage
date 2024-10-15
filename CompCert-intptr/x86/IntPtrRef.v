Require Import BoolEqual.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Maps.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import sflib Classical.
Require Import IntPtrRel.
Require Import Op PointerOp.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v2, <<_ :Some ?v1 = Some v2>> /\ <<_: val_intptr _ _ v2>> ] =>
      esplits; eauto
  | _ => idtac
  end.

Ltac InvBind :=
  match goal with
  | [ H: val_intptr _ (Vint _) _ |- _ ] =>
      inv H; InvBind
  | [ H:  val_intptr _ (Vfloat _) _ |- _ ] =>
      inv H; InvBind
  | [ H: val_intptr _ (Vptr _ _) _ |- _ ] =>
      inv H; InvBind
  | [ H: val_intptrist _ nil _ |- _ ] =>
      inv H; InvBind
  | [ H: val_intptrist _ (_ :: _) _ |- _ ] =>
      inv H; InvBind
  | _ => idtac
  end.

Section EVAL_WRAPPER_REFINE.

Variable F V: Type.
Variable genv: Genv.t F V.

Lemma eval_condition_binded_no_ptr_binary
    m m' vl vl' c b
    (NOTPTR: ptr_cond c = false)
    (CONCEXT: concrete_extends m m')
    (BIND: val_intptrist m' vl vl')
    (COND: eval_condition c vl m = Some b) :
  <<COND: eval_condition c vl' m' = Some b>>.
Proof.
  assert (SAMEVLD: forall b ofs, Mem.valid_pointer m b ofs = true -> Mem.valid_pointer m' b ofs = true).
  { eapply valid_concrete_extends; eauto. }
  destruct BIND; ss. destruct BIND.
  { inv H; destruct c; ss. }
  destruct BIND; [|ss]. inv H; inv H0; ss; destruct c; ss.
Qed.

Lemma select_binded
    ob ob' m m' v1 v1' v2 v2' ty
    (OB: ob = None \/ ob = ob')
    (CONCEXT: concrete_extends m m')
    (BIND1: val_intptr m' v1 v1')
    (BIND2: val_intptr m' v2 v2') :
  <<BIND: val_intptr m' (Val.select ob v1 v2 ty) (Val.select ob' v1' v2' ty)>>.
Proof.
  intros; unfold Val.select. destruct OB.
- subst ob; auto. econs.
- subst ob'; destruct ob as [b|]; auto.
  2: { econs. }
  eapply normalize_binded; eauto. destruct b; auto.
Qed.

Lemma symbol_address_binded m id ofs :
  val_intptr m (Genv.symbol_address genv id ofs) (Genv.symbol_address genv id ofs).
Proof.
  intros. unfold Genv.symbol_address. destruct (Genv.find_symbol genv id) eqn:?; auto; econs.
Qed.

Lemma eval_addressing32_binded addr sp vl1 vl2 m2 v1
    (BIND: val_intptrist m2 vl1 vl2)
    (EVAL: eval_addressing32 genv sp addr vl1 = Some v1) :
  exists v2, <<EVAL: eval_addressing32 genv sp addr vl2 = Some v2>>
      /\ <<BIND: val_intptr m2 v1 v2>>.
Proof.
  destruct addr; simpl in *; FuncInv; InvBind; TrivialExists; try (by econs).
  - eapply add_bind; eauto. econs; eauto.
  - eapply add_bind; eauto; [eapply add_bind; eauto|econs; eauto].
  - eapply add_bind; eauto; [|econs; eauto].
    eapply mul_bind; eauto. econs; eauto.
  - do 2 (eapply add_bind; eauto); [|econs; eauto].
    eapply mul_bind; eauto. econs; eauto.
  - eapply symbol_address_binded.
  - eapply add_bind; eauto. eapply symbol_address_binded.
  - eapply add_bind; eauto; [eapply symbol_address_binded|eapply mul_bind]; eauto; econs.
  - unfold Val.offset_ptr. destruct sp; econs; eauto.
Qed.

Lemma eval_addressing64_binded addr sp vl1 vl2 m2 v1
  (BIND: val_intptrist m2 vl1 vl2)
  (EVAL: eval_addressing64 genv sp addr vl1 = Some v1) :
  exists v2, <<EVAL: eval_addressing64 genv sp addr vl2 = Some v2>>
      /\ <<BIND: val_intptr m2 v1 v2>>.
Proof.
  destruct addr; simpl in *; FuncInv; InvBind; TrivialExists; try (by econs).
  - eapply addl_bind; eauto. econs; eauto.
  - eapply addl_bind; eauto; [eapply addl_bind; eauto|econs; eauto].
  - eapply addl_bind; eauto; [|econs; eauto].
    eapply mull_bind; eauto. econs; eauto.
  - do 2 (eapply addl_bind; eauto); [|econs; eauto].
    eapply mull_bind; eauto. econs; eauto.
  - eapply symbol_address_binded.
  - unfold Val.offset_ptr. destruct sp; econs; eauto.
Qed.

Lemma eval_addressing_binded addr sp vl1 vl2 m2 v1
    (BIND: val_intptrist m2 vl1 vl2)
    (EVAL: eval_addressing genv sp addr vl1 = Some v1) :
  exists v2, <<EVAL: eval_addressing genv sp addr vl2 = Some v2>>
      /\ <<BIND: val_intptr m2 v1 v2>>.
Proof.
  unfold eval_addressing in *. destruct Archi.ptr64.
- eapply eval_addressing64_binded; eauto.
- eapply eval_addressing32_binded; eauto.
Qed.

Lemma to_ptr_null_id m v
  (NULL: to_ptr_val m v = Vnullptr) : v = Vnullptr.
Proof.
  unfold to_ptr_val, Mem.to_ptr in *. destruct v; simpl in *.
  2:{ destruct Archi.ptr64 eqn:SF; simpl in *; [inv NULL|].
      destruct (Int.eq i Int.zero) eqn:A; [|des_ifs]. eapply Int.same_if_eq in A.
      subst; eauto. ss. }
  2:{ destruct Archi.ptr64 eqn:SF; simpl in *;[|inv NULL].
      destruct (Int64.eq i Int64.zero) eqn:A; [|des_ifs].
      eapply Int64.same_if_eq in A. subst. eauto. }
  all: inv NULL.
Qed.
  
Lemma psubl_to_ptr_binded m m' v1 v1' v2 v2' v
    (BIT: Archi.ptr64 = true)
    (CONCEXT: concrete_extends m m')
    (BIND1: val_intptr m' v1 v1')
    (BIND2: val_intptr m' v2 v2')
    (PSUB: Val.psubl (to_ptr_val m v1) (to_ptr_val m v2) = v) :
  <<PSUBP: exists v', Val.psubl (to_ptr_val m' v1') (to_ptr_val m' v2') = v'
               /\ val_intptr m' v v'>> \/
  <<PSUBI: exists v', Val.psubl (to_int_val m' v1') (to_int_val m' v2') = v'
               /\ val_intptr m' v v'>>.
Proof.
  unfold Val.psubl in PSUB. rewrite BIT in PSUB.
  destruct (to_ptr_val m v1) eqn:TOPTR1; subst; try (by (left; esplits; eauto; econs)).
  { exploit to_ptr_val_ptr_or_undef; eauto. i. des; try by inv H.
    rewrite H in TOPTR1. exploit to_ptr_null_id; eauto. i. subst.
    destruct (to_ptr_val m v2) eqn:TOPTR2; subst; try (by (left; esplits; eauto; econs)).
    exploit to_ptr_val_ptr_or_undef; eauto. i. des; try by inv H0.
    rewrite H0 in TOPTR2. exploit to_ptr_null_id; eauto. i. subst.
    right. esplits; eauto.
    assert (v1' = Vnullptr /\ v2' = Vnullptr).
    { inv BIND1; inv BIND2. des_ifs. }
    des; subst. unfold to_int_val, Mem.to_int. unfold Vnullptr in *. rewrite BIT in *.
    simpl. simpl in *. rewrite BIT. inv H. inv H0. econs. }
  destruct (to_ptr_val m v2) eqn:TOPTR2; subst; try (by (left; esplits; eauto; econs)).
  destruct (eq_block b b0); simpl in *; cycle 1.
  { left. esplits; eauto. econs. }
  subst b0. unfold to_ptr_val, Mem.to_ptr in *. rewrite BIT in *.
  destruct v1; simpl in *;[clarify|clarify|simpl in *|clarify|clarify|simpl in *].
  - destruct v2; simpl in *;[clarify|clarify|simpl in *|clarify|clarify|simpl in *].
    (* int int *)
    + inv BIND1; inv BIND2; simpl in *. left.
      destruct (Int64.eq i1 Int64.zero) eqn:NULL1; simpl in *; [clarify| ].
      destruct (Int64.eq i2 Int64.zero) eqn:NULL2; simpl in *; [clarify| ].
      destruct (Mem.denormalize (Int64.unsigned i1) m) eqn:DENO1; simpl in *; [|clarify].
      destruct (Mem.denormalize (Int64.unsigned i2) m) eqn:DENO2; simpl in *; [|clarify].
      destruct p; destruct p0. simpl in *. inv TOPTR1; inv TOPTR2.
      exploit denormalize_concrete_extends; try eapply DENO1; eauto. intros TOPTR1'.
      exploit denormalize_concrete_extends; try eapply DENO2; eauto. intros TOPTR2'. des.
      rewrite TOPTR1', TOPTR2'. simpl. rewrite BIT. simpl.
      destruct (eq_block b b); [|contradiction]. esplits; eauto. econs.
    (* int ptr *)
    + destruct (Int64.eq i1 Int64.zero) eqn:NULL1; simpl in *; [clarify| ].
      inv BIND1. inv TOPTR2.
      destruct (Mem.denormalize (Int64.unsigned i1) m) eqn:DENO1; simpl in *; [|clarify].
      destruct p. simpl in *. inv TOPTR1.
      exploit denormalize_concrete_extends; try eapply DENO1; eauto. intros TOPTR1'. des.
      rewrite TOPTR1'. simpl. inv BIND2; simpl in *;[|clarify|]; rewrite BIT.
      * left. rewrite NULL1. simpl. rewrite BIT; simpl.
        destruct (eq_block b b); [|contradiction]. esplits; eauto. econs.
      * right. destruct (Mem.ptr2int b (Ptrofs.unsigned i0) m') eqn:P2I; cycle 1.
        { clarify. }
        rewrite BIT in *. inv H3. eapply Mem.denormalize_info in TOPTR1'. des.
        unfold Mem.ptr2int in P2I. rewrite CONC in P2I. inv P2I. esplits; eauto.
        assert ((Ptrofs.to_int64 (Ptrofs.sub (Ptrofs.repr (Int64.unsigned i1 - caddr)) i0))
                = (Int64.sub i1 (Int64.repr (caddr + Ptrofs.unsigned i0)))).
        { unfold Ptrofs.sub, Ptrofs.to_int64, Int64.sub.
          eapply Int64.same_if_eq. unfold Int64.eq.
          do 3 rewrite Int64.unsigned_repr_eq. do 2 rewrite Ptrofs.unsigned_repr_eq.
          eapply Ptrofs.modulus_eq64 in BIT. rewrite BIT.
          rewrite Zminus_mod_idemp_r. rewrite Zminus_mod_idemp_l. rewrite Z.mod_mod.
          2:{ specialize Int64.modulus_pos. lia. }
          replace (Int64.unsigned i1 - caddr - Ptrofs.unsigned i0)
            with (Int64.unsigned i1 - (caddr + Ptrofs.unsigned i0)) by lia. des_ifs; lia. }
        rewrite H. econs.
  - destruct v2; simpl in *;[clarify|clarify|simpl in *|clarify|clarify|simpl in *].
    (* ptr int *)
    + destruct (Int64.eq i2 Int64.zero) eqn:NULL2; simpl in *; [clarify| ].
      inv BIND2. inv TOPTR1.
      destruct (Mem.denormalize (Int64.unsigned i2) m) eqn:DENO2; simpl in *; [|clarify].
      destruct p. simpl in *. inv TOPTR2.
      exploit denormalize_concrete_extends; try eapply DENO2; eauto. intros TOPTR2'. des.
      rewrite TOPTR2'. simpl. inv BIND1; simpl in *;[|clarify|]; rewrite BIT.
      * left. rewrite NULL2. simpl.
        destruct (eq_block b b); [|contradiction]. esplits; eauto. econs.
      * right. destruct (Mem.ptr2int b (Ptrofs.unsigned i) m') eqn:P2I; cycle 1; [clarify|].
        rewrite BIT in *. inv H3. eapply Mem.denormalize_info in TOPTR2'. des.
        unfold Mem.ptr2int in P2I. rewrite CONC in P2I. inv P2I. esplits; eauto.
        assert (Ptrofs.to_int64 (Ptrofs.sub i (Ptrofs.repr (Int64.unsigned i2 - caddr)))
                = Int64.sub (Int64.repr (caddr + Ptrofs.unsigned i)) i2).
        { unfold Ptrofs.sub, Ptrofs.to_int64, Int64.sub. eapply Int64.same_if_eq. unfold Int64.eq.
          do 3 rewrite Int64.unsigned_repr_eq. do 2 rewrite Ptrofs.unsigned_repr_eq.
          eapply Ptrofs.modulus_eq64 in BIT. rewrite BIT.
          rewrite Zminus_mod_idemp_r. rewrite Zminus_mod_idemp_l. rewrite Z.mod_mod.
          2:{ specialize Int64.modulus_pos. lia. }
          replace (Ptrofs.unsigned i - (Int64.unsigned i2 - caddr))
            with (caddr + Ptrofs.unsigned i - Int64.unsigned i2) by lia. des_ifs; lia. }
        rewrite H. econs.
    (* ptr ptr *)
    + unfold Val.psubl. simpl. inv TOPTR1; inv TOPTR2.
      inv BIND1; [|clarify|].
      * inv BIND2; [|clarify|].
        { simpl. rewrite BIT. destruct (eq_block b b); [|contradiction]. left.
          esplits; eauto. econs. }
        { right. unfold to_int_val, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *. rewrite BIT in *.
          destruct ((Mem.mem_concrete m') ! b) eqn:CONC; inv H3. simpl. esplits; eauto.
          assert (Ptrofs.to_int64 (Ptrofs.sub i i0)
                  = Int64.sub (Int64.repr (z + Ptrofs.unsigned i)) (Int64.repr (z + Ptrofs.unsigned i0))).
          { unfold Ptrofs.sub, Ptrofs.to_int64, Int64.sub. eapply Int64.same_if_eq. unfold Int64.eq.
            repeat rewrite Int64.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
            eapply Ptrofs.modulus_eq64 in BIT. rewrite BIT.
            rewrite Zminus_mod_idemp_r. rewrite Zminus_mod_idemp_l. rewrite Z.mod_mod.
            2:{ specialize Int64.modulus_pos. lia. }
            replace (Ptrofs.unsigned i - Ptrofs.unsigned i0) with (z + Ptrofs.unsigned i - (z + Ptrofs.unsigned i0)) by lia.
            des_ifs; lia. }
          rewrite H. econs. }
      * inv BIND2; [|clarify|].
        { right. unfold to_int_val, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *. rewrite BIT in *.
          destruct ((Mem.mem_concrete m') ! b) eqn:CONC; inv H3. simpl.
          esplits; eauto.
          assert (Ptrofs.to_int64 (Ptrofs.sub i i0)
                  = Int64.sub (Int64.repr (z + Ptrofs.unsigned i)) (Int64.repr (z + Ptrofs.unsigned i0))).
          { unfold Ptrofs.sub, Ptrofs.to_int64, Int64.sub. eapply Int64.same_if_eq. unfold Int64.eq.
            repeat rewrite Int64.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
            eapply Ptrofs.modulus_eq64 in BIT. rewrite BIT.
            rewrite Zminus_mod_idemp_r. rewrite Zminus_mod_idemp_l. rewrite Z.mod_mod.
            2:{ specialize Int64.modulus_pos. lia. }
            replace (Ptrofs.unsigned i - Ptrofs.unsigned i0) with (z + Ptrofs.unsigned i - (z + Ptrofs.unsigned i0)) by lia.
            des_ifs; lia. }
          rewrite H. econs. }
        { right. unfold to_int_val, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
          destruct ((Mem.mem_concrete m') ! b) eqn:CONC; [| inv H3].
          rewrite BIT in *. inv H3. inv H5. simpl. esplits; eauto.
          assert (Ptrofs.to_int64 (Ptrofs.sub i i0)
                  = Int64.sub (Int64.repr (z + Ptrofs.unsigned i)) (Int64.repr (z + Ptrofs.unsigned i0))).
          { unfold Ptrofs.sub, Ptrofs.to_int64, Int64.sub. eapply Int64.same_if_eq. unfold Int64.eq.
            repeat rewrite Int64.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
            eapply Ptrofs.modulus_eq64 in BIT. rewrite BIT.
            rewrite Zminus_mod_idemp_r. rewrite Zminus_mod_idemp_l. rewrite Z.mod_mod.
            2:{ specialize Int64.modulus_pos. lia. }
            replace (Ptrofs.unsigned i - Ptrofs.unsigned i0) with (z + Ptrofs.unsigned i - (z + Ptrofs.unsigned i0)) by lia.
            des_ifs; lia. }
          rewrite H. econs. }
Qed.

Lemma psubl_to_int_binded
    m m' v1 v1' v2 v2' v
    (BIT: Archi.ptr64 = true)
    (CONCEXT: concrete_extends m m')
    (BIND1: val_intptr m' v1 v1')
    (BIND2: val_intptr m' v2 v2')
    (PSUB: Val.psubl (to_int_val m v1) (to_int_val m v2) = v) :
  <<PSUBI: exists v', Val.psubl (to_int_val m' v1') (to_int_val m' v2') = v'
               /\ val_intptr m' v v'>>.
Proof.
  unfold Val.psubl in PSUB. rewrite BIT in PSUB.
  destruct (to_int_val m v1) eqn:TOINT1; clarify; try (by (esplits; eauto; econs)).
  2:{ eapply to_int_val_int_or_undef in TOINT1. des; clarify. }
  destruct (to_int_val m v2) eqn:TOINT2; clarify; try (by (esplits; eauto; econs)); ss.
  exploit to_int_bind; try eapply BIND1; eauto. intros IBIND1.
  exploit to_int_bind; try eapply BIND2; eauto. intros IBIND2. des.
  rewrite TOINT1 in IBIND1. rewrite TOINT2 in IBIND2. inv IBIND1; inv IBIND2.
  esplits; eauto. econs.
Qed.

Lemma psub_to_ptr_binded
    m m' v1 v1' v2 v2' v
    (BIT: Archi.ptr64 = false)
    (CONCEXT: concrete_extends m m')
    (BIND1: val_intptr m' v1 v1')
    (BIND2: val_intptr m' v2 v2')
    (PSUB: Val.psub (to_ptr_val m v1) (to_ptr_val m v2) = v) :
  <<PSUBP: exists v', Val.psub (to_ptr_val m' v1') (to_ptr_val m' v2') = v'
               /\ val_intptr m' v v'>> \/
  <<PSUBI: exists v', Val.psub (to_int_val m' v1') (to_int_val m' v2') = v'
               /\ val_intptr m' v v'>>.
Proof.
  unfold Val.psub in PSUB. rewrite BIT in PSUB.
  destruct (to_ptr_val m v1) eqn:TOPTR1; subst; try (by (left; esplits; eauto; econs)).
  { exploit to_ptr_val_ptr_or_undef; eauto. i. des; [inv H|inv H|].
    rewrite H in TOPTR1. exploit to_ptr_null_id; eauto. i. subst.
    destruct (to_ptr_val m v2) eqn:TOPTR2; subst; try (by (left; esplits; eauto; econs)).
    exploit to_ptr_val_ptr_or_undef; eauto. i. des; [inv H|inv H|].
    rewrite H0 in TOPTR2. exploit to_ptr_null_id; eauto. i. subst. right. esplits; eauto.
    assert (v1' = Vnullptr /\ v2' = Vnullptr).
    { inv BIND1; inv BIND2. des_ifs. }
    des; subst. unfold to_int_val, Mem.to_int. unfold Vnullptr in *. rewrite BIT in *.
    simpl. simpl in *. rewrite BIT. inv H. inv H0. econs. }
  destruct (to_ptr_val m v2) eqn:TOPTR2; subst; try (by (left; esplits; eauto; econs)).
  destruct (eq_block b b0); simpl in *; cycle 1.
  { left. esplits; eauto. econs. }
  subst b0. unfold to_ptr_val, Mem.to_ptr in *. rewrite BIT in *.
  destruct v1; simpl in *;[clarify|simpl in *|clarify|clarify|clarify|simpl in *].
  - destruct v2; simpl in *;[clarify|simpl in *|clarify|clarify|clarify|simpl in *].
    (* int int *)
    + inv BIND1; inv BIND2; simpl in *. left.
      destruct (Int.eq i1 Int.zero) eqn:NULL1; simpl in *; [clarify| ].
      destruct (Int.eq i2 Int.zero) eqn:NULL2; simpl in *; [clarify| ].
      destruct (Mem.denormalize (Int.unsigned i1) m) eqn:DENO1; simpl in *; [|clarify].
      destruct (Mem.denormalize (Int.unsigned i2) m) eqn:DENO2; simpl in *; [|clarify].
      destruct p; destruct p0. simpl in *. inv TOPTR1; inv TOPTR2.
      exploit denormalize_concrete_extends; try eapply DENO1; eauto. intros TOPTR1'.
      exploit denormalize_concrete_extends; try eapply DENO2; eauto. intros TOPTR2'. des.
      rewrite TOPTR1', TOPTR2'. simpl. rewrite BIT. simpl.
      destruct (eq_block b b); [|contradiction]. esplits; eauto. econs.
    (* int ptr *)
    + inv BIND1. inv TOPTR2.
      destruct (Int.eq i1 Int.zero) eqn:NULL1; simpl in *; [clarify| ].
      destruct (Mem.denormalize (Int.unsigned i1) m) eqn:DENO1; simpl in *; [|clarify].
      destruct p. simpl in *. inv TOPTR1.
      exploit denormalize_concrete_extends; try eapply DENO1; eauto. intros TOPTR1'. des.
      rewrite TOPTR1'. simpl. inv BIND2; simpl in *;[| |clarify]; rewrite BIT.
      * left. destruct (eq_block b b); [|contradiction]. esplits; eauto. econs.
      * right. destruct (Mem.ptr2int b (Ptrofs.unsigned i0) m') eqn:P2I; cycle 1; [clarify|].
        rewrite BIT in *. inv H3. eapply Mem.denormalize_info in TOPTR1'. des.
        unfold Mem.ptr2int in P2I. rewrite CONC in P2I. inv P2I. esplits; eauto.
        assert ((Ptrofs.to_int (Ptrofs.sub (Ptrofs.repr (Int.unsigned i1 - caddr)) i0))
                = (Int.sub i1 (Int.repr (caddr + Ptrofs.unsigned i0)))).
        { unfold Ptrofs.sub, Ptrofs.to_int, Int.sub.
          eapply Int.same_if_eq. unfold Int.eq.
          do 3 rewrite Int.unsigned_repr_eq. do 2 rewrite Ptrofs.unsigned_repr_eq.
          eapply Ptrofs.modulus_eq32 in BIT. rewrite BIT.
          rewrite Zminus_mod_idemp_r. rewrite Zminus_mod_idemp_l. rewrite Z.mod_mod.
          2:{ specialize Int.modulus_pos. lia. }
          replace (Int.unsigned i1 - caddr - Ptrofs.unsigned i0)
            with (Int.unsigned i1 - (caddr + Ptrofs.unsigned i0)) by lia. des_ifs; lia. }
        rewrite H. econs.
  - destruct v2; simpl in *;[clarify|simpl in *|clarify|clarify|clarify|simpl in *].
    (* ptr int *)
    + inv BIND2. inv TOPTR1.
      destruct (Int.eq i2 Int.zero) eqn:NULL2; simpl in *; [clarify| ].
      destruct (Mem.denormalize (Int.unsigned i2) m) eqn:DENO2; simpl in *; [|clarify].
      destruct p. simpl in *. inv TOPTR2.
      exploit denormalize_concrete_extends; try eapply DENO2; eauto. intros TOPTR2'. des.
      rewrite TOPTR2'. simpl. inv BIND1; simpl in *;[| |clarify]; rewrite BIT.
      * left. destruct (eq_block b b); [|contradiction]. esplits; eauto. econs.
      * right. destruct (Mem.ptr2int b (Ptrofs.unsigned i) m') eqn:P2I; cycle 1;[clarify|].
        rewrite BIT in *. inv H3. eapply Mem.denormalize_info in TOPTR2'. des.
        unfold Mem.ptr2int in P2I. rewrite CONC in P2I. inv P2I. esplits; eauto.
        assert (Ptrofs.to_int (Ptrofs.sub i (Ptrofs.repr (Int.unsigned i2 - caddr)))
                = Int.sub (Int.repr (caddr + Ptrofs.unsigned i)) i2).
        { unfold Ptrofs.sub, Ptrofs.to_int, Int.sub. eapply Int.same_if_eq. unfold Int.eq.
          do 3 rewrite Int.unsigned_repr_eq. do 2 rewrite Ptrofs.unsigned_repr_eq.
          eapply Ptrofs.modulus_eq32 in BIT. rewrite BIT.
          rewrite Zminus_mod_idemp_r. rewrite Zminus_mod_idemp_l. rewrite Z.mod_mod.
          2:{ specialize Int.modulus_pos. lia. }
          replace (Ptrofs.unsigned i - (Int.unsigned i2 - caddr))
            with (caddr + Ptrofs.unsigned i - Int.unsigned i2) by lia. des_ifs; lia. }
        rewrite H. econs.
    (* ptr ptr *)
    + unfold Val.psub. simpl. inv TOPTR1; inv TOPTR2.
      inv BIND1; [| |clarify].
      * inv BIND2; [| |clarify].
        { simpl. rewrite BIT. destruct (eq_block b b); [|contradiction]. left.
          esplits; eauto. econs. }
        { right. unfold to_int_val, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *. rewrite BIT in *.
          destruct ((Mem.mem_concrete m') ! b) eqn:CONC; inv H3. simpl. esplits; eauto.
          assert (Ptrofs.to_int (Ptrofs.sub i i0)
                  = Int.sub (Int.repr (z + Ptrofs.unsigned i)) (Int.repr (z + Ptrofs.unsigned i0))).
          { unfold Ptrofs.sub, Ptrofs.to_int, Int.sub. eapply Int.same_if_eq. unfold Int.eq.
            repeat rewrite Int.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
            eapply Ptrofs.modulus_eq32 in BIT. rewrite BIT.
            rewrite Zminus_mod_idemp_r. rewrite Zminus_mod_idemp_l. rewrite Z.mod_mod.
            2:{ specialize Int.modulus_pos. lia. }
            replace (Ptrofs.unsigned i - Ptrofs.unsigned i0)
              with (z + Ptrofs.unsigned i - (z + Ptrofs.unsigned i0)) by lia. des_ifs; lia. }
          rewrite H. econs. }
      * inv BIND2; [| |clarify].
        { right. unfold to_int_val, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *. rewrite BIT in *.
          destruct ((Mem.mem_concrete m') ! b) eqn:CONC; inv H3. simpl. esplits; eauto.
          assert (Ptrofs.to_int (Ptrofs.sub i i0)
                  = Int.sub (Int.repr (z + Ptrofs.unsigned i)) (Int.repr (z + Ptrofs.unsigned i0))).
          { unfold Ptrofs.sub, Ptrofs.to_int, Int.sub. eapply Int.same_if_eq. unfold Int.eq.
            repeat rewrite Int.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
            eapply Ptrofs.modulus_eq32 in BIT. rewrite BIT.
            rewrite Zminus_mod_idemp_r. rewrite Zminus_mod_idemp_l. rewrite Z.mod_mod.
            2:{ specialize Int.modulus_pos. lia. }
            replace (Ptrofs.unsigned i - Ptrofs.unsigned i0)
              with (z + Ptrofs.unsigned i - (z + Ptrofs.unsigned i0)) by lia. des_ifs; lia. }
          rewrite H. econs. }
        { right. unfold to_int_val, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
          destruct ((Mem.mem_concrete m') ! b) eqn:CONC; [|inv H3].
          rewrite BIT in *. inv H3. inv H5. simpl. esplits; eauto.
          assert (Ptrofs.to_int (Ptrofs.sub i i0)
                  = Int.sub (Int.repr (z + Ptrofs.unsigned i)) (Int.repr (z + Ptrofs.unsigned i0))).
          { unfold Ptrofs.sub, Ptrofs.to_int, Int.sub. eapply Int.same_if_eq. unfold Int.eq.
            repeat rewrite Int.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
            eapply Ptrofs.modulus_eq32 in BIT. rewrite BIT.
            rewrite Zminus_mod_idemp_r. rewrite Zminus_mod_idemp_l. rewrite Z.mod_mod.
            2:{ specialize Int.modulus_pos. lia. }
            replace (Ptrofs.unsigned i - Ptrofs.unsigned i0)
              with (z + Ptrofs.unsigned i - (z + Ptrofs.unsigned i0)) by lia. des_ifs; lia. }
          rewrite H. econs. }
Qed.

Lemma psub_to_int_binded
    m m' v1 v1' v2 v2' v
    (BIT: Archi.ptr64 = false)
    (CONCEXT: concrete_extends m m')
    (BIND1: val_intptr m' v1 v1')
    (BIND2: val_intptr m' v2 v2')
    (PSUB: Val.psub (to_int_val m v1) (to_int_val m v2) = v) :
  <<PSUBI: exists v', Val.psub (to_int_val m' v1') (to_int_val m' v2') = v'
               /\ val_intptr m' v v'>>.
Proof.
  unfold Val.psub in PSUB. rewrite BIT in PSUB.
  destruct (to_int_val m v1) eqn:TOINT1; inversion PSUB; try (by (esplits; eauto; econs)).
  2:{ eapply to_int_val_int_or_undef in TOINT1. des; clarify. }
  destruct (to_int_val m v2) eqn:TOINT2; inversion PSUB; try (by (esplits; eauto; econs)).
  exploit to_int_bind; try eapply BIND1; eauto. intros IBIND1.
  exploit to_int_bind; try eapply BIND2; eauto. intros IBIND2. des.
  rewrite TOINT1 in IBIND1. rewrite TOINT2 in IBIND2. inv IBIND1; inv IBIND2.
  esplits; eauto. unfold Val.psub. rewrite BIT. econs.
Qed.

Lemma psub_only_int_and_undef v1 v2: Val.psub v1 v2 = Vundef \/ exists n, Val.psub v1 v2 = Vint n.
Proof. unfold Val.psub in *. des_ifs; eauto. Qed.

Lemma psubl_only_long_and_undef v1 v2: Val.psubl v1 v2 = Vundef \/ exists n, Val.psubl v1 v2 = Vlong n.
Proof. unfold Val.psubl in *. des_ifs; eauto. Qed.

Lemma cmpu_bool_to_ptr_binded
    m m' v1 v1' v2 v2' c b
    (CONCEXT: concrete_extends m m')
    (BIND1: val_intptr m' v1 v1')
    (BIND2: val_intptr m' v2 v2')
    (CMP: Val.cmpu_bool (Mem.valid_pointer m) c (to_ptr_val m v1) (to_ptr_val m v2) = Some b) :
  <<CMPP: Val.cmpu_bool (Mem.valid_pointer m') c (to_ptr_val m' v1') (to_ptr_val m' v2') = Some b>>
  \/ <<CMPI: Val.cmpu_bool (Mem.valid_pointer m') c (to_int_val m' v1') (to_int_val m' v2') = Some b>>.
Proof.
  assert (SAMEVLD: forall b ofs, Mem.valid_pointer m b ofs = true -> Mem.valid_pointer m' b ofs = true).
  { eapply valid_concrete_extends; eauto. }
  destruct Archi.ptr64 eqn:BIT.
  { unfold Val.cmpu_bool in CMP. rewrite BIT in *; des_ifs;
    unfold to_ptr_val, Mem.to_ptr in Heq, Heq0; rewrite BIT in *; des_ifs. }
  unfold Val.cmpu_bool in CMP. rewrite BIT in CMP.
  destruct (to_ptr_val m v1) eqn:TOPTR1; try inversion CMP.
  { exploit to_ptr_val_ptr_or_undef; eauto. i. des; [clarify|clarify|].
    rewrite H in TOPTR1. exploit to_ptr_null_id; eauto. i. subst.
    destruct (to_ptr_val m v2) eqn:TOPTR2; subst; try inversion CMP.
    { exploit to_ptr_val_ptr_or_undef; eauto. i. des; [clarify|clarify|].
      rewrite H1 in TOPTR2. exploit to_ptr_null_id; eauto. i. subst. right. esplits; eauto.
      assert (v1' = Vnullptr /\ v2' = Vnullptr).
      { inv BIND1; inv BIND2. des_ifs. }
      des; subst. unfold to_int_val, Mem.to_int. unfold Vnullptr in *. rewrite BIT in *.
      simpl. simpl in *. inv H. inv H1. econs. }
    simpl in *. assert (Int.eq i Int.zero = true) by (unfold Vnullptr in H; des_ifs).
    rewrite H1 in *. simpl in *. clear H0.
    destruct (Mem.valid_pointer m b1 (Ptrofs.unsigned i0) ||
              Mem.valid_pointer m b1 (Ptrofs.unsigned i0 - 1)) eqn:WVLD; [|inv CMP].
    assert (v1' = Vnullptr) by (inv BIND1; des_ifs). subst. unfold to_ptr_val in *.
    destruct v2; simpl in *; [clarify|simpl in *|rewrite BIT in *; simpl in *; clarify|clarify|clarify|simpl in *].
    { inv BIND2. destruct (Int.eq i1 Int.zero) eqn:A; simpl in  *. { inv TOPTR2. }
      destruct (Mem.denormalize (Int.unsigned i1) m) eqn:DENO; simpl in  *; [|inv TOPTR2].
      destruct p; simpl in *. exploit denormalize_concrete_extends; eauto. i. des. rewrite BIT, A, H0.
      left. unfold Val.cmplu_bool, Mem.to_ptr, Vnullptr in *. rewrite BIT, Int.eq_true in *. simpl.
      simpl in TOPTR2. inv TOPTR2. exploit weak_valid_concrete_extends; eauto. i.
      unfold Mem.weak_valid_pointer in H3. rewrite BIT, Int.eq_true. simpl. rewrite H3. eauto. }
    inv TOPTR2. inv BIND2; [ | |clarify].
    { unfold Mem.to_ptr, Vnullptr. rewrite BIT, Int.eq_true. simpl. rewrite BIT, Int.eq_true. simpl.
      left. exploit weak_valid_concrete_extends; eauto. i. unfold Mem.weak_valid_pointer in H0.
      rewrite H0. eauto. }
    { unfold Mem.ptr2int_v in H6. destruct (Mem.ptr2int b1 (Ptrofs.unsigned i0) m') eqn:I2P;[|clarify].
      rewrite BIT in *. inv H6. exploit weak_valid_concrete_extends; eauto. intros WVLD'.
      exploit Mem.ptr2int_weak_valid; eauto; [eapply Ptrofs.unsigned_range_2|]. i. inv H0. simpl in *.
      assert (Int.eq (Int.repr z) Int.zero = false).
      { unfold Int.eq. rewrite Int.unsigned_repr.
        2:{ unfold Int.max_unsigned. rewrite <- Ptrofs.modulus_eq32; eauto. lia. }
        destruct (zeq z (Int.unsigned Int.zero)) eqn:ZEQ;[|eauto]. subst.
        rewrite Int.unsigned_zero in FST. lia. }
      right. unfold Vnullptr. rewrite BIT. simpl.
      destruct c; simpl in *; inv CMP.
      { rewrite Int.eq_sym. rewrite I2P, BIT in H3. inv H3. rewrite H0. eauto. }
      { rewrite Int.eq_sym. rewrite I2P, BIT in H3. inv H3. rewrite H0. eauto. } } }
  destruct (to_ptr_val m v2) eqn:TOPTR2; try inversion CMP.
  { exploit to_ptr_val_ptr_or_undef; eauto. i. des; [clarify|clarify|].
    rewrite H in TOPTR2. exploit to_ptr_null_id; eauto. i. subst.
    assert (v2' = Vnullptr) by (inv BIND2; des_ifs). subst.
    destruct ((Mem.valid_pointer m b0 (Ptrofs.unsigned i) || Mem.valid_pointer m b0 (Ptrofs.unsigned i - 1))) eqn:WVLD.
    2:{ simpl in *. rewrite andb_false_r in CMP. inv CMP. }
    unfold to_ptr_val in *.
    destruct v1; simpl in *; [clarify|simpl in *|rewrite BIT in *; simpl in *; clarify|clarify|clarify|simpl in *].
    { inv BIND1. destruct (Int.eq i1 Int.zero) eqn:A; simpl in  *. { inv TOPTR1. }
      destruct (Mem.denormalize (Int.unsigned i1) m) eqn:DENO; simpl in  *;[|inv TOPTR1].
      destruct p; simpl in *. exploit denormalize_concrete_extends; eauto. i. des. rewrite BIT, A, H2.
      left. unfold Val.cmplu_bool, Mem.to_ptr, Vnullptr in *. rewrite BIT, Int.eq_true in *. simpl.
      simpl in TOPTR1. inv TOPTR1. exploit weak_valid_concrete_extends; eauto. i.
      unfold Mem.weak_valid_pointer in H3. inv H. rewrite BIT, Int.eq_true. simpl. rewrite H3. eauto. }
    inv TOPTR1. inv BIND1; [| |clarify].
    { unfold Mem.to_ptr, Vnullptr in *. rewrite BIT, Int.eq_true in *. simpl. rewrite BIT, Int.eq_true. simpl.
      left. inv H. exploit weak_valid_concrete_extends; eauto. i. unfold Mem.weak_valid_pointer in H.
      rewrite H. eauto. }
    { unfold Mem.ptr2int_v in H6. destruct (Mem.ptr2int b0 (Ptrofs.unsigned i) m') eqn:I2P;[|clarify].
      rewrite BIT in *. inv H6. exploit weak_valid_concrete_extends; eauto. intros WVLD'.
      exploit Mem.ptr2int_weak_valid; eauto; [eapply Ptrofs.unsigned_range_2|]. i. inv H2. simpl in *.
      assert (Int.eq (Int.repr z) Int.zero = false).
      { unfold Int.eq. rewrite Int.unsigned_repr.
        2:{ unfold Int.max_unsigned. rewrite <- Ptrofs.modulus_eq32; eauto. lia. }
        destruct (zeq z (Int.unsigned Int.zero)) eqn:ZEQ;[|eauto]. subst.
        rewrite Int.unsigned_zero in FST. lia. }
      right. unfold Vnullptr in *. rewrite BIT in *. simpl. inv H. rewrite Int.eq_true.
      destruct c; simpl in *; inv CMP.
      { rewrite I2P in H3. inv H3. rewrite H2. eauto. }
      { rewrite I2P in H3. inv H3. rewrite H2. eauto. } } }
  clear H0. destruct (eq_block b0 b1); subst.
  (* same block *)
  - fold (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i)) in *.
    fold (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i0)) in *.
    destruct (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i)
              && Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i0)) eqn:WVLD; [|inv CMP].
    inv CMP. unfold to_ptr_val in *.
    destruct v1; simpl in *; [clarify|simpl in *|rewrite BIT in *; simpl in *; clarify|clarify|clarify|simpl in *].
    + rewrite BIT in TOPTR1. simpl in TOPTR1.
      destruct v2; simpl in *; [clarify|simpl in *|rewrite BIT in *; simpl in *; clarify|clarify|clarify|simpl in *].
      * destruct (Mem.denormalize (Int.unsigned i1) m) eqn:DENO1; [|simpl in *; clarify].
        destruct (Mem.denormalize (Int.unsigned i2) m) eqn:DENO2; [|simpl in *; clarify].
        rewrite BIT in TOPTR2. simpl in *. destruct p; destruct p0. simpl in *.
        destruct (Int.eq i1 Int.zero) eqn:NULL1; simpl in *; [clarify| ].
        destruct (Int.eq i2 Int.zero) eqn:NULL2; simpl in *; [clarify| ].
        inv TOPTR1. inv TOPTR2. inv BIND1. inv BIND2. left. r. unfold Mem.to_ptr. rewrite BIT. simpl.
        exploit denormalize_concrete_extends; try apply DENO1; eauto. i.
        exploit denormalize_concrete_extends; try apply DENO2; eauto. i. des. rewrite H, H0.
        rewrite NULL1, NULL2. simpl. eapply andb_prop in WVLD. des.
        exploit weak_valid_concrete_extends; try eapply WVLD; eauto. intros WVLD'.
        exploit weak_valid_concrete_extends; try eapply WVLD0; eauto. intros WVLD0'.
        rewrite BIT. destruct (eq_block b1 b1); [|clarify].
        unfold Mem.weak_valid_pointer in WVLD', WVLD0'. rewrite WVLD', WVLD0'. eauto.
      * destruct (Mem.denormalize (Int.unsigned i1) m) eqn:DENO1.
        2:{ simpl in *. clarify. }
        destruct p. simpl in TOPTR1.
        destruct (Int.eq i1 Int.zero) eqn:NULL1; simpl in *; [clarify| ].
        inv TOPTR1. inv TOPTR2. inv BIND1. inv BIND2; [| | clarify].
        { left. exploit denormalize_concrete_extends; eauto. i. des. unfold Mem.to_ptr. rewrite BIT, H, NULL1. simpl.
          rewrite BIT. eapply andb_prop in WVLD. des.
          exploit weak_valid_concrete_extends; try eapply WVLD; eauto. intros WVLD'.
          exploit weak_valid_concrete_extends; try eapply WVLD0; eauto. intros WVLD0'.
          destruct (eq_block b1 b1); [|clarify].
          unfold Mem.weak_valid_pointer in WVLD', WVLD0'. rewrite WVLD', WVLD0'. eauto. }
        { right. simpl. eapply andb_prop in WVLD. destruct WVLD as [WVLD1 WVLD2]. unfold Mem.to_int, Mem.ptr2int_v in H4.
          destruct (Mem.ptr2int b1 (Ptrofs.unsigned i0) m') eqn:P2I; cycle 1; [inv H4|].
          rewrite BIT in H4. inv H4.
          exploit Mem.denormalize_info; eauto. i. des. subst.
          eapply weak_valid_concrete_extends in WVLD2; eauto.
          exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|].
          i. des. eapply extended_concrete in CONC; eauto. rewrite CONC0 in CONC. inv CONC.
          inv INRANGE. simpl in *.
          assert (LT: Int.ltu i1 (Int.repr (caddr + Ptrofs.unsigned i0))
                      = Ptrofs.ltu (Ptrofs.repr (Int.unsigned i1 - caddr)) i0).
          { unfold Ptrofs.ltu, Int.ltu. rewrite Ptrofs.unsigned_repr; [| lia].
            rewrite Ptrofs.modulus_eq32 in SND; eauto. rewrite Int.unsigned_repr; [| unfold Int.max_unsigned; lia].
            des_ifs; lia. }
          assert (EQ: Int.eq i1 (Int.repr (caddr + Ptrofs.unsigned i0))
                      = Ptrofs.eq (Ptrofs.repr (Int.unsigned i1 - caddr)) i0).
          { unfold Ptrofs.eq, Int.eq. rewrite Ptrofs.unsigned_repr; [| lia].
            rewrite Ptrofs.modulus_eq32 in SND; eauto. rewrite Int.unsigned_repr; [| unfold Int.max_unsigned; lia].
            des_ifs; lia. }
          symmetry. f_equal. eapply lt_eq_cmpu; eauto. }
    + inversion TOPTR1; subst.
      destruct v2; simpl in *; [clarify|simpl in *|rewrite BIT in *; simpl in *; clarify|clarify|clarify|simpl in *].
      * destruct (Mem.denormalize (Int.unsigned i1) m) eqn:DENO2; [|simpl in *; clarify].
        destruct p. rewrite BIT in TOPTR2. simpl in TOPTR2.
        destruct (Int.eq i1 Int.zero) eqn:NULL1; simpl in *; [clarify| ].
        inv TOPTR2. inv TOPTR1. inv BIND2. inv BIND1; [| |clarify].
        { left. exploit denormalize_concrete_extends; eauto. i. des. unfold Mem.to_ptr. rewrite BIT, H, NULL1. simpl.
          rewrite BIT. eapply andb_prop in WVLD. des.
          exploit weak_valid_concrete_extends; try eapply WVLD; eauto. intros WVLD'.
          exploit weak_valid_concrete_extends; try eapply WVLD0; eauto. intros WVLD0'.
          destruct (eq_block b1 b1); [|clarify].
          unfold Mem.weak_valid_pointer in WVLD', WVLD0'. rewrite WVLD', WVLD0'. eauto. }
        { right. simpl. eapply andb_prop in WVLD. destruct WVLD as [WVLD1 WVLD2]. unfold Mem.to_int, Mem.ptr2int_v in H4.
          destruct (Mem.ptr2int b1 (Ptrofs.unsigned i) m') eqn:P2I; cycle 1; [inv H4|].
          rewrite BIT in H4. inv H4.
          exploit Mem.denormalize_info; eauto. i. des. subst.
          eapply weak_valid_concrete_extends in WVLD1; eauto.
          exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|].
          i. des. eapply extended_concrete in CONC; eauto. rewrite CONC0 in CONC. inv CONC.
          inv INRANGE. simpl in *.
          assert (LT: Int.ltu (Int.repr (caddr + Ptrofs.unsigned i)) i1
                      = Ptrofs.ltu i (Ptrofs.repr (Int.unsigned i1 - caddr))).
          { unfold Ptrofs.ltu, Int.ltu. rewrite Ptrofs.unsigned_repr; [| lia].
            rewrite Ptrofs.modulus_eq32 in SND; eauto. rewrite Int.unsigned_repr; [| unfold Int.max_unsigned; lia].
            des_ifs; lia. }
          assert (EQ: Int.eq (Int.repr (caddr + Ptrofs.unsigned i)) i1
                      = Ptrofs.eq i (Ptrofs.repr (Int.unsigned i1 - caddr))).
          { unfold Ptrofs.eq, Int.eq. rewrite Ptrofs.unsigned_repr; [| lia].
            rewrite Ptrofs.modulus_eq32 in SND; eauto. rewrite Int.unsigned_repr; [| unfold Int.max_unsigned; lia].
            des_ifs; lia. }
          symmetry. f_equal. eapply lt_eq_cmpu; eauto. }
      * inv TOPTR2. eapply andb_prop in WVLD. destruct WVLD as [WVLD1 WVLD2].
        inv BIND1; [ | | clarify].
        { inv BIND2; [ | | clarify].
          - left. simpl. rewrite BIT. destruct (eq_block b1 b1); [|clarify].
            exploit weak_valid_concrete_extends; try eapply WVLD1; eauto. intros WVLD1'.
            exploit weak_valid_concrete_extends; try eapply WVLD2; eauto. intros WVLD2'.
            unfold Mem.weak_valid_pointer in WVLD1', WVLD2'.
            rewrite WVLD1', WVLD2'; eauto.
          - right. unfold Mem.to_int, Mem.ptr2int_v in H4.
            destruct (Mem.ptr2int b1 (Ptrofs.unsigned i0) m') eqn:P2I; cycle 1;[clarify|].
            rewrite BIT in H4. inv H4. eapply weak_valid_concrete_extends in WVLD2; eauto.
            exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|].
            i. des. subst. simpl. unfold to_int_val. simpl.
            assert (I2P': Mem.ptr2int b1 (Ptrofs.unsigned i) m' = Some (caddr + (Ptrofs.unsigned i))).
            { unfold Mem.ptr2int. rewrite CONC. eauto. }
            eapply weak_valid_concrete_extends in WVLD1; eauto.
            exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|].
            i. des. rewrite I2P', BIT. simpl. inv INRANGE; inv INRANGE0. simpl in *.
            assert (LT: Int.ltu (Int.repr (caddr + Ptrofs.unsigned i)) (Int.repr (caddr + Ptrofs.unsigned i0))
                        = Ptrofs.ltu i i0).
            { unfold Ptrofs.ltu, Int.ltu. rewrite Ptrofs.modulus_eq32 in *; eauto.
              do 2 (rewrite Int.unsigned_repr; [| unfold Int.max_unsigned; lia]).
              des_ifs; lia. }
            assert (EQ: Int.eq (Int.repr (caddr + Ptrofs.unsigned i)) (Int.repr (caddr + Ptrofs.unsigned i0))
                        = Ptrofs.eq i i0).
            { unfold Ptrofs.eq, Int.eq. rewrite Ptrofs.modulus_eq32 in *; eauto.
              do 2 (rewrite Int.unsigned_repr; [| unfold Int.max_unsigned; lia]).
              des_ifs; lia. }
            symmetry. f_equal. eapply lt_eq_cmpu; eauto. }
        { inv BIND2; [ | | clarify].
          - right. unfold Mem.to_int, Mem.ptr2int_v in H4.
            destruct (Mem.ptr2int b1 (Ptrofs.unsigned i) m') eqn:P2I; cycle 1;[clarify|].
            rewrite BIT in H4. inv H4. eapply weak_valid_concrete_extends in WVLD1; eauto.
            exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|].
            i. des. subst. unfold to_int_val. simpl.
            assert (I2P': Mem.ptr2int b1 (Ptrofs.unsigned i0) m' = Some (caddr + (Ptrofs.unsigned i0))).
            { unfold Mem.ptr2int. rewrite CONC. eauto. }
            eapply weak_valid_concrete_extends in WVLD2; eauto.
            exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|].
            i. des. rewrite I2P', BIT. simpl. inv INRANGE; inv INRANGE0. simpl in *.
            assert (LT: Int.ltu (Int.repr (caddr + Ptrofs.unsigned i)) (Int.repr (caddr + Ptrofs.unsigned i0))
                        = Ptrofs.ltu i i0).
            { unfold Ptrofs.ltu, Int.ltu. rewrite Ptrofs.modulus_eq32 in *; eauto.
              do 2 (rewrite Int.unsigned_repr; [| unfold Int.max_unsigned; lia]).
              des_ifs; lia. }
            assert (EQ: Int.eq (Int.repr (caddr + Ptrofs.unsigned i)) (Int.repr (caddr + Ptrofs.unsigned i0))
                        = Ptrofs.eq i i0).
            { unfold Ptrofs.eq, Int.eq. rewrite Ptrofs.modulus_eq32 in *; eauto.
              do 2 (rewrite Int.unsigned_repr; [| unfold Int.max_unsigned; lia]).
              des_ifs; lia. }
            symmetry. f_equal. eapply lt_eq_cmpu; eauto.
          - right. unfold Mem.to_int, Mem.ptr2int_v in *.
            destruct (Mem.ptr2int b1 (Ptrofs.unsigned i) m') eqn:I2P; cycle 1; [inv H3|].
            destruct (Mem.ptr2int b1 (Ptrofs.unsigned i0) m') eqn:I2P'; cycle 1; [inv H3|].
            rewrite BIT in H4, H6. inv H4; inv H6.
            eapply weak_valid_concrete_extends in WVLD1; eauto.
            eapply weak_valid_concrete_extends in WVLD2; eauto.
            exploit Mem.ptr2int_weak_valid'; try eapply I2P; eauto; [eapply Ptrofs.unsigned_range_2|].
            exploit Mem.ptr2int_weak_valid'; try eapply I2P'; eauto; [eapply Ptrofs.unsigned_range_2|].
            i. des. subst. simpl. inv INRANGE; inv INRANGE0. simpl in *.
            assert (LT: Int.ltu (Int.repr (caddr + Ptrofs.unsigned i)) (Int.repr (caddr0 + Ptrofs.unsigned i0))
                        = Ptrofs.ltu i i0).
            { unfold Ptrofs.ltu, Int.ltu. rewrite Ptrofs.modulus_eq32 in *; eauto.
              do 2 (rewrite Int.unsigned_repr; [| unfold Int.max_unsigned; lia]).
              des_ifs; lia. }
            assert (EQ: Int.eq (Int.repr (caddr + Ptrofs.unsigned i)) (Int.repr (caddr0 + Ptrofs.unsigned i0))
                        = Ptrofs.eq i i0).
            { unfold Ptrofs.eq, Int.eq. rewrite Ptrofs.modulus_eq32 in *; eauto.
              do 2 (rewrite Int.unsigned_repr; [| unfold Int.max_unsigned; lia]).
              des_ifs; lia. }
            symmetry. f_equal. eapply lt_eq_cmpu; eauto. }
  (* diff block *)
  - destruct (Mem.valid_pointer m b0 (Ptrofs.unsigned i) && Mem.valid_pointer m b1 (Ptrofs.unsigned i0)) eqn:VLD;
    [| clarify]. unfold to_ptr_val in *.
    destruct v1; simpl in *; [clarify|rewrite BIT in *; simpl in *|simpl in *; clarify|clarify|clarify|simpl in *].
    + destruct v2; simpl in *; [clarify|simpl in *|rewrite BIT in *; simpl in *; clarify|clarify|clarify|simpl in *].
      * destruct (Mem.denormalize (Int.unsigned i1) m) eqn:DENO1; [|simpl in *; clarify].
        destruct (Mem.denormalize (Int.unsigned i2) m) eqn:DENO2; [|simpl in *; clarify].
        rewrite BIT in TOPTR2. simpl in *. destruct p; destruct p0. simpl in *.
        destruct (Int.eq i1 Int.zero) eqn:NULL1; simpl in *; [clarify| ].
        destruct (Int.eq i2 Int.zero) eqn:NULL2; simpl in *; [clarify| ].
        inv TOPTR1. inv TOPTR2.
        inv BIND1. inv BIND2. left. r. unfold Mem.to_ptr. rewrite BIT, NULL1, NULL2. simpl.
        exploit denormalize_concrete_extends; try apply DENO1; eauto. i.
        exploit denormalize_concrete_extends; try apply DENO2; eauto. i. des. rewrite H, H0. simpl.
        eapply andb_prop in VLD. des.
        exploit valid_concrete_extends; try eapply VLD; eauto. intros VLD'.
        exploit valid_concrete_extends; try eapply VLD0; eauto. intros VLD0'.
        rewrite BIT. destruct (eq_block b0 b1); [subst; clarify|].
        rewrite VLD', VLD0'. eauto.
      * destruct (Mem.denormalize (Int.unsigned i1) m) eqn:DENO1; [|simpl in *; clarify].
        destruct p. simpl in TOPTR1.
        destruct (Int.eq i1 Int.zero) eqn:NULL1; simpl in *; [clarify| ].
        inv TOPTR1. inv TOPTR2. inv BIND1. inv BIND2; [| |clarify].
        { left. exploit denormalize_concrete_extends; eauto. i. des. unfold Mem.to_ptr. rewrite BIT, H, NULL1. simpl.
          rewrite BIT. eapply andb_prop in VLD. des.
          exploit valid_concrete_extends; try eapply VLD; eauto. intros VLD'.
          exploit valid_concrete_extends; try eapply VLD0; eauto. intros VLD0'.
          destruct (eq_block b0 b1); [subst; clarify|]. rewrite VLD', VLD0'. eauto. }
        { simpl. eapply andb_prop in VLD. destruct VLD as [VLD1 VLD2]. unfold Mem.to_int, Mem.ptr2int_v in H4.
          destruct (Mem.ptr2int b1 (Ptrofs.unsigned i0) m') eqn:P2I; cycle 1;[inv H4|].
          rewrite BIT in H4. inv H4. exploit Mem.denormalize_info; eauto. i. des. subst. 
          assert (INBLK1: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (Int.unsigned i1) b0).
          { eapply Mem.conditions_of_addr_in_block; eauto. }
          exploit Mem.valid_pointer_implies; try eapply VLD2. i.
          eapply weak_valid_concrete_extends in H; eauto.
          exploit Mem.ptr2int_weak_valid'; eauto;[eapply Ptrofs.unsigned_range_2|].
          i. des. subst. inv INRANGE. simpl in *.
          assert (INBLK2: Mem.addr_in_block (Mem.mem_concrete m') (Mem.mem_access m') (caddr0 + Ptrofs.unsigned i0) b1).
          { eapply Mem.conditions_of_addr_in_block; eauto.
            - replace (caddr0 + Ptrofs.unsigned i0 - caddr0) with (Ptrofs.unsigned i0) by lia.
              eapply SAMEVLD in VLD2. rewrite Mem.valid_pointer_nonempty_perm in VLD2; eauto.
              eapply Mem.perm_cur_max. eauto.
            - replace (caddr0 + Ptrofs.unsigned i0 - caddr0) with (Ptrofs.unsigned i0) by lia.
              eapply Ptrofs.unsigned_range_2. }
          assert (INBLK1': Mem.addr_in_block (Mem.mem_concrete m') (Mem.mem_access m') (Int.unsigned i1) b0).
          { inv INBLK1. econs; eauto; [eapply extended_concrete; eauto|].
            des. exploit extended_access; eauto. i. unfold Mem.perm, Mem.perm_order' in H0. des_ifs; eauto. }
          exploit Ptrofs.modulus_eq32; eauto. i.
          assert (Int.eq i1 (Int.repr (caddr0 + Ptrofs.unsigned i0)) = false).
          { unfold Int.eq. rewrite Int.unsigned_repr.
            2:{ unfold Int.max_unsigned. rewrite <- H0. lia. }
            destruct (zeq (Int.unsigned i1) (caddr0 + Ptrofs.unsigned i0)) eqn:ZEQ;[|eauto].
            { rewrite <- e in INBLK2. exfalso. eapply n. eapply Mem.no_concrete_overlap; eauto. } }
          destruct c; simpl in *; inversion CMP; (right; rewrite H3; eauto). }
    + inversion TOPTR1; subst.
      destruct v2; simpl in *; [clarify|simpl in *|rewrite BIT in *; simpl in *; clarify|clarify|clarify|simpl in *].
      * destruct (Mem.denormalize (Int.unsigned i1) m) eqn:DENO2; [|simpl in *; clarify].
        destruct p. simpl in TOPTR2. rewrite BIT in TOPTR2. simpl in *.
        destruct (Int.eq i1 Int.zero) eqn:NULL1; simpl in *; [clarify| ].
        inv TOPTR2. inv BIND2. inv BIND1; [| |clarify].
        { left. exploit denormalize_concrete_extends; eauto. i. des. unfold Mem.to_ptr. rewrite BIT, H, NULL1. simpl.
          rewrite BIT. eapply andb_prop in VLD. des.
          exploit valid_concrete_extends; try eapply VLD; eauto. intros VLD'.
          exploit valid_concrete_extends; try eapply VLD0; eauto. intros VLD0'.
          destruct (eq_block b0 b1); [subst; clarify|]. rewrite VLD', VLD0'. eauto. }
        { simpl. eapply andb_prop in VLD. destruct VLD as [VLD1 VLD2]. unfold Mem.to_int, Mem.ptr2int_v in H4.
          destruct (Mem.ptr2int b0 (Ptrofs.unsigned i) m') eqn:P2I; cycle 1; [inv H4|].
          rewrite BIT in H4. inv H4.
          exploit Mem.denormalize_info; eauto. i. des. subst. 
          assert (INBLK1: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (Int.unsigned i1) b1).
          { eapply Mem.conditions_of_addr_in_block; eauto. }
          exploit Mem.valid_pointer_implies; try eapply VLD1. i.
          eapply weak_valid_concrete_extends in H; eauto.
          exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|].
          i. des. subst. inv INRANGE. simpl in *.
          assert (INBLK2: Mem.addr_in_block (Mem.mem_concrete m') (Mem.mem_access m') (caddr0 + Ptrofs.unsigned i) b0).
          { eapply Mem.conditions_of_addr_in_block; eauto.
            - replace (caddr0 + Ptrofs.unsigned i - caddr0) with (Ptrofs.unsigned i) by lia.
              eapply SAMEVLD in VLD1. rewrite Mem.valid_pointer_nonempty_perm in VLD1; eauto.
              eapply Mem.perm_cur_max. eauto.
            - replace (caddr0 + Ptrofs.unsigned i - caddr0) with (Ptrofs.unsigned i) by lia.
              eapply Ptrofs.unsigned_range_2. }
          assert (INBLK1': Mem.addr_in_block (Mem.mem_concrete m') (Mem.mem_access m') (Int.unsigned i1) b1).
          { inv INBLK1. econs; eauto; [eapply extended_concrete; eauto|].
            des. exploit extended_access; eauto. i. unfold Mem.perm, Mem.perm_order' in H0. des_ifs; eauto. }
          exploit Ptrofs.modulus_eq32; eauto. i.
          assert (Int.eq (Int.repr (caddr0 + Ptrofs.unsigned i)) i1 = false).
          { unfold Int.eq. rewrite Int.unsigned_repr; [|unfold Int.max_unsigned; rewrite <- H0; lia].
            destruct (zeq (caddr0 + Ptrofs.unsigned i) (Int.unsigned i1)) eqn:ZEQ;[|eauto].
            { rewrite e in INBLK2. exfalso. eapply n. eapply Mem.no_concrete_overlap; eauto. } }
          destruct c; simpl in *; inversion CMP; right; rewrite H3; eauto. }
      * inv TOPTR2. eapply andb_prop in VLD. destruct VLD as [VLD1 VLD2].
        inv BIND1; [ | | clarify].
        { inv BIND2; [ | | clarify].
          - simpl. rewrite BIT. destruct (eq_block b0 b1); [subst;clarify|].
            eapply SAMEVLD in VLD1, VLD2. rewrite VLD1, VLD2. simpl. eauto.
          - unfold Mem.to_int, Mem.ptr2int_v in H4.
            destruct (Mem.ptr2int b1 (Ptrofs.unsigned i0) m') eqn:P2I;[|inv H4].
            rewrite BIT in *. inv H4. exploit Mem.ptr2int_to_denormalize; eauto.
            { eapply Ptrofs.unsigned_range_2. }
            i. des. exploit Mem.denormalize_paddr_in_range; eauto.  i. inv H0.
            unfold fst, snd in *.
            left. simpl. rewrite BIT. simpl. rewrite Int.unsigned_repr.
            2:{ unfold Int.max_unsigned. rewrite <- Ptrofs.modulus_eq32; eauto. lia. }
            destruct (Int.eq (Int.repr z) Int.zero) eqn:NULL.
            { eapply Mem.denormalized_not_nullptr32 in H; eauto. clarify. }
            simpl. rewrite H. simpl. destruct (eq_block b0 b1); [subst; clarify|].
            eapply SAMEVLD in VLD1, VLD2. rewrite Ptrofs.repr_unsigned.
            rewrite VLD1, VLD2. simpl. eauto. }
        { inv BIND2; [ | | clarify].
          - unfold Mem.to_int, Mem.ptr2int_v in H4.
            destruct (Mem.ptr2int b0 (Ptrofs.unsigned i) m') eqn:P2I; [|inv H4].
            rewrite BIT in *. inv H4. exploit Mem.ptr2int_to_denormalize; eauto.
            { eapply Ptrofs.unsigned_range_2. }
            i. des. exploit Mem.denormalize_paddr_in_range; eauto. i. inv H0.
            unfold fst, snd in *.
            left. simpl. rewrite BIT. simpl. rewrite Int.unsigned_repr.
            2:{ unfold Int.max_unsigned. rewrite <- Ptrofs.modulus_eq32; eauto. lia. }
            destruct (Int.eq (Int.repr z) Int.zero) eqn:NULL.
            { eapply Mem.denormalized_not_nullptr32 in H; eauto. clarify. }
            simpl.  rewrite H. simpl. destruct (eq_block b0 b1); [subst; clarify|].
            eapply SAMEVLD in VLD1, VLD2. rewrite Ptrofs.repr_unsigned. rewrite VLD1, VLD2.
            rewrite BIT. eauto.
          - unfold Mem.to_int, Mem.ptr2int_v in H4, H6.
            destruct (Mem.ptr2int b0 (Ptrofs.unsigned i) m') eqn:P2I;[|inv H4].
            destruct (Mem.ptr2int b1 (Ptrofs.unsigned i0) m') eqn:P2I';[|inv H6].
            rewrite BIT in *. inv H4; inv H6.
            exploit Mem.ptr2int_to_denormalize; try eapply P2I; eauto; i.
            { eapply Ptrofs.unsigned_range_2. }
            exploit Mem.ptr2int_to_denormalize; try eapply P2I'; eauto; i; des.
            { eapply Ptrofs.unsigned_range_2. }
            exploit Mem.denormalize_paddr_in_range; try eapply H; eauto. i. inv H4.
            exploit Mem.denormalize_paddr_in_range; try eapply H0; eauto. i. inv H4.
            unfold fst, snd in *. left. simpl. rewrite BIT. simpl.
            rewrite Int.unsigned_repr.
            2:{ unfold Int.max_unsigned. rewrite <- Ptrofs.modulus_eq32; eauto. lia. }
            rewrite Int.unsigned_repr.
            2:{ unfold Int.max_unsigned. rewrite <- Ptrofs.modulus_eq32; eauto. lia. }
            destruct (Int.eq (Int.repr z) Int.zero) eqn:NULL.
            { eapply Mem.denormalized_not_nullptr32 in H; eauto. clarify. }
            simpl. destruct (Int.eq (Int.repr z0) Int.zero) eqn:NULL'.
            { eapply Mem.denormalized_not_nullptr32 in H; eauto. clarify. }
            simpl. rewrite H, H0. simpl. rewrite BIT. destruct (eq_block b0 b1); [subst; clarify|].
            eapply SAMEVLD in VLD1, VLD2. do 2 rewrite Ptrofs.repr_unsigned. rewrite VLD1, VLD2. eauto. }
Qed.

Lemma cmpu_bool_to_int_binded
  m m' v1 v1' v2 v2' c b
  (CONCEXT: concrete_extends m m')
  (BIND1: val_intptr m' v1 v1')
  (BIND2: val_intptr m' v2 v2')
  (CMP: Val.cmpu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2) = Some b) :
  <<CMPI: Val.cmpu_bool (Mem.valid_pointer m') c (to_int_val m' v1') (to_int_val m' v2') = Some b>>.
Proof.
  destruct Archi.ptr64 eqn:BIT.
  { unfold Val.cmpu_bool in CMP. rewrite BIT in *; des_ifs
    ;unfold to_int_val, Mem.to_int in Heq, Heq0; des_ifs; simpl in *; clarify; des_ifs;
      inv BIND1; inv BIND2; simpl; eauto. }
  unfold Val.cmpu_bool in CMP. rewrite BIT in CMP.
  destruct (to_int_val m v1) eqn:TOINT1; inversion CMP.
  2:{ eapply to_int_val_int_or_undef in TOINT1. des; clarify. }
  destruct (to_int_val m v2) eqn:TOINT2; inv CMP.
  2:{ eapply to_int_val_int_or_undef in TOINT1. des; clarify. }
  exploit to_int_bind; try eapply BIND1; eauto. intros IBIND1.
  exploit to_int_bind; try eapply BIND2; eauto. intros IBIND2. des.
  rewrite TOINT1 in IBIND1. rewrite TOINT2 in IBIND2. inv IBIND1; inv IBIND2.
  simpl. eauto.
Qed.

Lemma cmplu_bool_to_ptr_binded
    m m' v1 v1' v2 v2' c b
    (CONCEXT: concrete_extends m m')
    (BIND1: val_intptr m' v1 v1')
    (BIND2: val_intptr m' v2 v2')
    (CMP: Val.cmplu_bool (Mem.valid_pointer m) c (to_ptr_val m v1) (to_ptr_val m v2) = Some b) :
  <<CMPP: Val.cmplu_bool (Mem.valid_pointer m') c (to_ptr_val m' v1') (to_ptr_val m' v2') = Some b>>
  \/ <<CMPI: Val.cmplu_bool (Mem.valid_pointer m') c (to_int_val m' v1') (to_int_val m' v2') = Some b>>.
Proof.
  assert (SAMEVLD: forall b ofs, Mem.valid_pointer m b ofs = true -> Mem.valid_pointer m' b ofs = true).
  { eapply valid_concrete_extends; eauto. }
  destruct Archi.ptr64 eqn:BIT.
  2:{ unfold Val.cmplu_bool in CMP. rewrite BIT in *; des_ifs;
      unfold to_ptr_val, Mem.to_ptr in Heq, Heq0; rewrite BIT in *; des_ifs. }
  unfold Val.cmplu_bool in CMP. rewrite BIT in CMP.
  destruct (to_ptr_val m v1) eqn:TOPTR1; try inversion CMP.
  { exploit to_ptr_val_ptr_or_undef; eauto. i. des; try by inv H.
    rewrite H in TOPTR1. exploit to_ptr_null_id; eauto. i. subst.
    destruct (to_ptr_val m v2) eqn:TOPTR2; subst; try by inv H0.
    { exploit to_ptr_val_ptr_or_undef; eauto. i. des; try by inv H1.
      rewrite H1 in TOPTR2. exploit to_ptr_null_id; eauto. i. subst. right. esplits; eauto.
      assert (v1' = Vnullptr /\ v2' = Vnullptr).
      { inv BIND1; inv BIND2. des_ifs. }
      des; subst. unfold to_int_val, Mem.to_int. unfold Vnullptr in *. rewrite BIT in *.
      simpl. simpl in *. inv H. inv H1. econs. }
    simpl in *. assert (Int64.eq i Int64.zero = true) by (unfold Vnullptr in H; des_ifs).
    rewrite H1 in *. simpl in *. clear H0.
    destruct (Mem.valid_pointer m b1 (Ptrofs.unsigned i0)
              || Mem.valid_pointer m b1 (Ptrofs.unsigned i0 - 1)) eqn:WVLD; [|inv CMP].
    assert (v1' = Vnullptr) by (inv BIND1; des_ifs). subst. unfold to_ptr_val in *.
    destruct v2; simpl in *; [clarify|clarify|rewrite BIT in *; simpl in *; clarify|clarify|clarify|simpl in *].
    { inv BIND2. destruct (Int64.eq i1 Int64.zero) eqn:A; simpl in  *. { inv TOPTR2. }
      destruct (Mem.denormalize (Int64.unsigned i1) m) eqn:DENO; simpl in  *; [|inv TOPTR2].
      destruct p; simpl in *. exploit denormalize_concrete_extends; eauto. i. des. rewrite BIT, A, H0.
      left. unfold Val.cmplu_bool, Mem.to_ptr, Vnullptr in *. rewrite BIT, Int64.eq_true in *. simpl.
      exploit weak_valid_concrete_extends; try eapply WVLD; eauto. intros WVLD'.
      inv TOPTR2. unfold Mem.weak_valid_pointer in WVLD'. rewrite WVLD', Int64.eq_true. simpl; eauto. }
    inv TOPTR2. inv BIND2; [|clarify|].
    { unfold Mem.to_ptr, Vnullptr. rewrite BIT, Int64.eq_true. simpl. rewrite BIT, Int64.eq_true. simpl.
      left. exploit weak_valid_concrete_extends; try eapply WVLD; eauto. intros WVLD'.
      unfold Mem.weak_valid_pointer in WVLD'. rewrite WVLD'. eauto. }
    { simpl in H5. unfold Mem.ptr2int_v in H5. destruct (Mem.ptr2int b1 (Ptrofs.unsigned i0) m') eqn:I2P;[|clarify].
      rewrite BIT in *. inv H5. eapply weak_valid_concrete_extends in WVLD; eauto.
      exploit Mem.ptr2int_weak_valid; eauto; [eapply Ptrofs.unsigned_range_2|]. i. inv H0. simpl in *.
      assert (Int64.eq (Int64.repr z) Int64.zero = false).
      { unfold Int64.eq. rewrite Int64.unsigned_repr.
        2:{ unfold Int64.max_unsigned. rewrite <- Ptrofs.modulus_eq64; eauto. lia. }
        destruct (zeq z (Int64.unsigned Int64.zero)) eqn:ZEQ;[|eauto]. subst.
        rewrite Int64.unsigned_zero in FST. lia. }
      right. unfold Vnullptr. rewrite BIT. simpl.
      destruct c; simpl in *; inv CMP; rewrite Int64.eq_sym; rewrite H0; eauto. } }
  destruct (to_ptr_val m v2) eqn:TOPTR2; try inversion CMP.
  { exploit to_ptr_val_ptr_or_undef; eauto. i. des; [clarify|clarify|].
    rewrite H in TOPTR2. exploit to_ptr_null_id; eauto. i. subst.
    assert (v2' = Vnullptr) by (inv BIND2; des_ifs). subst.
    destruct ((Mem.valid_pointer m b0 (Ptrofs.unsigned i) || Mem.valid_pointer m b0 (Ptrofs.unsigned i - 1))) eqn:WVLD.
    2:{ simpl in *. rewrite andb_false_r in CMP. inv CMP. }
    unfold to_ptr_val in *.
    destruct v1; simpl in *; [clarify|clarify|rewrite BIT in *; simpl in *; clarify|clarify|clarify|simpl in *].
    { inv BIND1. destruct (Int64.eq i1 Int64.zero) eqn:A; simpl in  *. { inv TOPTR1. }
      destruct (Mem.denormalize (Int64.unsigned i1) m) eqn:DENO; simpl in  *; [|inv TOPTR1].
      destruct p; simpl in *. exploit denormalize_concrete_extends; eauto. i. des. rewrite BIT, A, H2.
      left. unfold Val.cmplu_bool, Mem.to_ptr, Vnullptr in *. rewrite BIT, Int64.eq_true in *. simpl.
      exploit weak_valid_concrete_extends; try eapply WVLD; eauto. intros WVLD'. inv TOPTR1.
      unfold Mem.weak_valid_pointer in WVLD'. rewrite WVLD', Int64.eq_true. inv H; simpl; eauto. }
    inv TOPTR1. inv BIND1; [|clarify|].
    { unfold Mem.to_ptr, Vnullptr in *. rewrite BIT, Int64.eq_true in *. simpl. rewrite BIT, Int64.eq_true. simpl.
      left. eapply weak_valid_concrete_extends in WVLD; eauto.
      unfold Mem.weak_valid_pointer in WVLD. rewrite WVLD. inv H; eauto. }
    { simpl in H6. unfold Mem.ptr2int_v in H6. destruct (Mem.ptr2int b0 (Ptrofs.unsigned i) m') eqn:I2P;[|clarify].
      rewrite BIT in *. inv H6. eapply weak_valid_concrete_extends in WVLD; eauto.
      exploit Mem.ptr2int_weak_valid; eauto; [eapply Ptrofs.unsigned_range_2|]. i. inv H2. simpl in *.
      assert (Int64.eq (Int64.repr z) Int64.zero = false).
      { unfold Int64.eq. rewrite Int64.unsigned_repr.
        2:{ unfold Int64.max_unsigned. rewrite <- Ptrofs.modulus_eq64; eauto. lia. }
        destruct (zeq z (Int64.unsigned Int64.zero)) eqn:ZEQ;[|eauto]. subst.
        rewrite Int64.unsigned_zero in FST. lia. }
      right. unfold Vnullptr in *. rewrite BIT in *. simpl. inv H. rewrite Int64.eq_true.
      destruct c; simpl in *; inv CMP; rewrite H2; eauto. } }
  clear H0. destruct (eq_block b0 b1); subst.
  (* same block *)
  - fold (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i)) in *.
    fold (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i0)) in *.
    destruct (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i)
              && Mem.weak_valid_pointer m b1 (Ptrofs.unsigned i0)) eqn:WVLD; [|inv CMP].
    inv CMP. unfold to_ptr_val in *.
    destruct v1; simpl in *; [clarify|clarify|rewrite BIT in *; simpl in *; clarify|clarify|clarify|simpl in *].
    + destruct v2; simpl in *; [clarify|clarify|rewrite BIT in *; simpl in *; clarify|clarify|clarify|simpl in *].
      * destruct (Int64.eq i1 Int64.zero) eqn:NULL1; simpl in *; [clarify| ].
        destruct (Int64.eq i2 Int64.zero) eqn:NULL2; simpl in *; [clarify| ].
        destruct (Mem.denormalize (Int64.unsigned i1) m) eqn:DENO1; [|simpl in *; clarify].
        destruct (Mem.denormalize (Int64.unsigned i2) m) eqn:DENO2; [|simpl in *; clarify].
        simpl in *. destruct p; destruct p0. simpl in *. inv TOPTR1. inv TOPTR2.
        inv BIND1. inv BIND2. left. r. unfold Mem.to_ptr. rewrite BIT. simpl.
        exploit denormalize_concrete_extends; try apply DENO1; eauto. i.
        exploit denormalize_concrete_extends; try apply DENO2; eauto. i. des. rewrite H, H0. simpl.
        rewrite NULL1, NULL2. simpl. eapply andb_prop in WVLD. des.
        eapply weak_valid_concrete_extends in WVLD, WVLD0; eauto.
        rewrite BIT. destruct (eq_block b1 b1); [|clarify].
        unfold Mem.weak_valid_pointer in WVLD, WVLD0. rewrite WVLD, WVLD0. eauto.
      * destruct (Int64.eq i1 Int64.zero) eqn:NULL1; simpl in *; [clarify| ].
        destruct (Mem.denormalize (Int64.unsigned i1) m) eqn:DENO1; [|simpl in *; clarify].
        destruct p. simpl in TOPTR1. inv TOPTR1. inv TOPTR2. inv BIND1. inv BIND2.
        { left. exploit denormalize_concrete_extends; eauto. i. des. unfold Mem.to_ptr. rewrite BIT, H, NULL1. simpl.
          rewrite BIT. eapply andb_prop in WVLD. des.
          eapply weak_valid_concrete_extends in WVLD, WVLD0; eauto.
          destruct (eq_block b1 b1); [|clarify].
          unfold Mem.weak_valid_pointer in WVLD, WVLD0. rewrite WVLD, WVLD0. eauto. }
        { clarify. }
        { right. simpl. eapply andb_prop in WVLD. destruct WVLD as [WVLD1 WVLD2]. simpl in H4. unfold Mem.ptr2int_v in H4.
          destruct (Mem.ptr2int b1 (Ptrofs.unsigned i0) m') eqn:P2I; cycle 1; [inv H4|].
          rewrite BIT in H4. inv H4. exploit Mem.denormalize_info; eauto. i. des. subst.
          eapply weak_valid_concrete_extends in WVLD2; eauto.
          exploit Mem.ptr2int_weak_valid'; eauto.
          { eapply Ptrofs.unsigned_range_2. }
          i. des. eapply extended_concrete in CONC; eauto. rewrite CONC0 in CONC. inv CONC.
          inv INRANGE. simpl in *.
          assert (LT: Int64.ltu i1 (Int64.repr (caddr + Ptrofs.unsigned i0))
                      = Ptrofs.ltu (Ptrofs.repr (Int64.unsigned i1 - caddr)) i0).
          { unfold Ptrofs.ltu, Int64.ltu. rewrite Ptrofs.unsigned_repr; [| lia].
           rewrite Ptrofs.modulus_eq64 in SND; eauto. rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; lia].
            des_ifs; lia. }
          assert (EQ: Int64.eq i1 (Int64.repr (caddr + Ptrofs.unsigned i0))
                      = Ptrofs.eq (Ptrofs.repr (Int64.unsigned i1 - caddr)) i0).
          { unfold Ptrofs.eq, Int64.eq. rewrite Ptrofs.unsigned_repr; [| lia].
            rewrite Ptrofs.modulus_eq64 in SND; eauto. rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; lia].
            des_ifs; lia. }
          symmetry. f_equal. eapply lt_eq_cmplu; eauto. }
    + inversion TOPTR1; subst.
      destruct v2; simpl in *; [clarify|clarify|rewrite BIT in *; simpl in *; clarify|clarify|clarify|simpl in *].
      * destruct (Int64.eq i1 Int64.zero) eqn:NULL2; simpl in *; [clarify| ].
        destruct (Mem.denormalize (Int64.unsigned i1) m) eqn:DENO2; [|simpl in *; clarify].
        destruct p. simpl in TOPTR2. inv TOPTR2. inv TOPTR1. inv BIND2. inv BIND1;[|clarify|].
        { left. exploit denormalize_concrete_extends; eauto. i. des. unfold Mem.to_ptr. rewrite BIT, H, NULL2. simpl.
          rewrite BIT. eapply andb_prop in WVLD. des.
          eapply weak_valid_concrete_extends in WVLD, WVLD0; eauto.
          repeat rewrite <- SAMEVLD. destruct (eq_block b1 b1); [|clarify].
          unfold Mem.weak_valid_pointer in WVLD, WVLD0. rewrite WVLD, WVLD0. eauto. }
        { right. simpl. eapply andb_prop in WVLD. destruct WVLD as [WVLD1 WVLD2]. simpl in H4. unfold Mem.ptr2int_v in H4.
          destruct (Mem.ptr2int b1 (Ptrofs.unsigned i) m') eqn:P2I; cycle 1; [inv H4|].
          rewrite BIT in H4. inv H4. exploit Mem.denormalize_info; eauto. i. des. subst.
          eapply weak_valid_concrete_extends in WVLD1; eauto.
          exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|].
          i. des. eapply extended_concrete in CONC; eauto. rewrite CONC0 in CONC. inv CONC.
          inv INRANGE. simpl in *.
          assert (LT: Int64.ltu (Int64.repr (caddr + Ptrofs.unsigned i)) i1
                      = Ptrofs.ltu i (Ptrofs.repr (Int64.unsigned i1 - caddr))).
          { unfold Ptrofs.ltu, Int64.ltu. rewrite Ptrofs.unsigned_repr; [| lia].
            rewrite Ptrofs.modulus_eq64 in SND; eauto. rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; lia].
            des_ifs; lia. }
          assert (EQ: Int64.eq (Int64.repr (caddr + Ptrofs.unsigned i)) i1
                      = Ptrofs.eq i (Ptrofs.repr (Int64.unsigned i1 - caddr))).
          { unfold Ptrofs.eq, Int64.eq. rewrite Ptrofs.unsigned_repr; [| lia].
            rewrite Ptrofs.modulus_eq64 in SND; eauto. rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; lia].
            des_ifs; lia. }
          symmetry. f_equal. eapply lt_eq_cmplu; eauto. }
      * inv TOPTR2. eapply andb_prop in WVLD. destruct WVLD as [WVLD1 WVLD2].
        inv BIND1; [ |clarify | ].
        { inv BIND2; [ | clarify | ].
          - left. simpl. rewrite BIT. destruct (eq_block b1 b1); [|clarify].
            eapply weak_valid_concrete_extends in WVLD1, WVLD2; eauto.
            unfold Mem.weak_valid_pointer in WVLD1, WVLD2. rewrite WVLD1, WVLD2; eauto.
          - right. simpl in H4. unfold Mem.ptr2int_v in H4.
            destruct (Mem.ptr2int b1 (Ptrofs.unsigned i0) m') eqn:P2I; cycle 1; [clarify|].
            rewrite BIT in H4. inv H4. eapply weak_valid_concrete_extends in WVLD2; eauto.
            exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|].
            i. des. subst. simpl. unfold to_int_val. simpl.
            assert (I2P': Mem.ptr2int b1 (Ptrofs.unsigned i) m' = Some (caddr + (Ptrofs.unsigned i))).
            { unfold Mem.ptr2int. rewrite CONC. eauto. }
            eapply weak_valid_concrete_extends in WVLD1; eauto.
            exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|].
            i. des. rewrite I2P', BIT. simpl. inv INRANGE; inv INRANGE0. simpl in *.
            assert (LT: Int64.ltu (Int64.repr (caddr + Ptrofs.unsigned i)) (Int64.repr (caddr + Ptrofs.unsigned i0))
                        = Ptrofs.ltu i i0).
            { unfold Ptrofs.ltu, Int64.ltu. rewrite Ptrofs.modulus_eq64 in *; eauto.
              do 2 (rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; lia]). des_ifs; lia. }
            assert (EQ: Int64.eq (Int64.repr (caddr + Ptrofs.unsigned i)) (Int64.repr (caddr + Ptrofs.unsigned i0))
                        = Ptrofs.eq i i0).
            { unfold Ptrofs.eq, Int64.eq. rewrite Ptrofs.modulus_eq64 in *; eauto.
              do 2 (rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; lia]). des_ifs; lia. }
            symmetry. f_equal. eapply lt_eq_cmplu; eauto. }
        { inv BIND2; [ | | clarify]; [|clarify|].
          - right. simpl in H4. unfold Mem.ptr2int_v in H4.
            destruct (Mem.ptr2int b1 (Ptrofs.unsigned i) m') eqn:P2I; cycle 1; [clarify|].
            rewrite BIT in H4. inv H4. eapply weak_valid_concrete_extends in WVLD1; eauto.
            exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|].
            i. des. subst. unfold to_int_val. simpl.
            assert (I2P': Mem.ptr2int b1 (Ptrofs.unsigned i0) m' = Some (caddr + (Ptrofs.unsigned i0))).
            { unfold Mem.ptr2int. rewrite CONC. eauto. }
            eapply weak_valid_concrete_extends in WVLD2; eauto.
            exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|].
            i. des. rewrite I2P', BIT. simpl. inv INRANGE; inv INRANGE0. simpl in *.
            assert (LT: Int64.ltu (Int64.repr (caddr + Ptrofs.unsigned i)) (Int64.repr (caddr + Ptrofs.unsigned i0))
                        = Ptrofs.ltu i i0).
            { unfold Ptrofs.ltu, Int64.ltu. rewrite Ptrofs.modulus_eq64 in *; eauto.
              do 2 (rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; lia]). des_ifs; lia. }
            assert (EQ: Int64.eq (Int64.repr (caddr + Ptrofs.unsigned i)) (Int64.repr (caddr + Ptrofs.unsigned i0))
                        = Ptrofs.eq i i0).
            { unfold Ptrofs.eq, Int64.eq. rewrite Ptrofs.modulus_eq64 in *; eauto.
              do 2 (rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; lia]). des_ifs; lia. }
            symmetry. f_equal. eapply lt_eq_cmplu; eauto.
          - right. simpl in *. unfold Mem.ptr2int_v in *.
            destruct (Mem.ptr2int b1 (Ptrofs.unsigned i) m') eqn:I2P; cycle 1;[inv H4|].
            destruct (Mem.ptr2int b1 (Ptrofs.unsigned i0) m') eqn:I2P'; cycle 1;[inv H6|].
            rewrite H3 in H4, H6. inv H4; inv H6.
            eapply weak_valid_concrete_extends in WVLD1; eauto.
            eapply weak_valid_concrete_extends in WVLD2; eauto.
            exploit Mem.ptr2int_weak_valid'; try eapply I2P; eauto; [eapply Ptrofs.unsigned_range_2|].
            exploit Mem.ptr2int_weak_valid'; try eapply I2P'; eauto; [eapply Ptrofs.unsigned_range_2|].
            i. des. subst. simpl. inv INRANGE; inv INRANGE0. simpl in *.
            assert (LT: Int64.ltu (Int64.repr (caddr + Ptrofs.unsigned i)) (Int64.repr (caddr0 + Ptrofs.unsigned i0))
                        = Ptrofs.ltu i i0).
            { unfold Ptrofs.ltu, Int64.ltu. rewrite Ptrofs.modulus_eq64 in *; eauto.
              do 2 (rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; lia]). des_ifs; lia. }
            assert (EQ: Int64.eq (Int64.repr (caddr + Ptrofs.unsigned i)) (Int64.repr (caddr0 + Ptrofs.unsigned i0))
                        = Ptrofs.eq i i0).
            { unfold Ptrofs.eq, Int64.eq. rewrite Ptrofs.modulus_eq64 in *; eauto.
              do 2 (rewrite Int64.unsigned_repr; [| unfold Int64.max_unsigned; lia]). des_ifs; lia. }
            symmetry. f_equal. eapply lt_eq_cmplu; eauto. }
  (* diff block *)
  - destruct (Mem.valid_pointer m b0 (Ptrofs.unsigned i) && Mem.valid_pointer m b1 (Ptrofs.unsigned i0)) eqn:VLD;
    [|clarify]. unfold to_ptr_val in *.
    destruct v1; simpl in *; [clarify|clarify; simpl in *|simpl in *; clarify|clarify|clarify|simpl in *].
    + destruct v2; simpl in *; [clarify|clarify|rewrite BIT in *; simpl in *; clarify|clarify|clarify|simpl in *].
      * destruct (Int64.eq i1 Int64.zero) eqn:NULL1; simpl in *; [clarify| ].
        destruct (Int64.eq i2 Int64.zero) eqn:NULL2; simpl in *; [clarify| ].
        destruct (Mem.denormalize (Int64.unsigned i1) m) eqn:DENO1; [|simpl in *; clarify].
        destruct (Mem.denormalize (Int64.unsigned i2) m) eqn:DENO2; [|simpl in *; clarify].
        simpl in *. destruct p; destruct p0. simpl in *. inv TOPTR1. inv TOPTR2.
        inv BIND1. inv BIND2. left. r. unfold Mem.to_ptr. rewrite BIT. simpl.
        exploit denormalize_concrete_extends; try apply DENO1; eauto. i.
        exploit denormalize_concrete_extends; try apply DENO2; eauto. i. des. rewrite H, H0, NULL1, NULL2. simpl.
        eapply andb_prop in VLD. des. eapply valid_concrete_extends in VLD, VLD0; eauto.
        rewrite BIT. destruct (eq_block b0 b1); [subst; clarify|]. rewrite VLD, VLD0. eauto.
      * destruct (Int64.eq i1 Int64.zero) eqn:NULL1; simpl in *; [clarify| ].
        destruct (Mem.denormalize (Int64.unsigned i1) m) eqn:DENO1; [|simpl in *; clarify].
        destruct p. simpl in TOPTR1. inv TOPTR1. inv TOPTR2. inv BIND1. inv BIND2;[|clarify|].
        { left. exploit denormalize_concrete_extends; eauto. i. des. unfold Mem.to_ptr. rewrite BIT, H, NULL1. simpl.
          rewrite BIT. eapply andb_prop in VLD. des. eapply valid_concrete_extends in VLD, VLD0; eauto.
          destruct (eq_block b0 b1); [subst; clarify|]. rewrite VLD, VLD0. eauto. }
        { simpl. eapply andb_prop in VLD. destruct VLD as [VLD1 VLD2]. simpl in H4. unfold Mem.ptr2int_v in H4.
          destruct (Mem.ptr2int b1 (Ptrofs.unsigned i0) m') eqn:P2I; cycle 1; [inv H4|].
          rewrite BIT in H4. inv H4. exploit Mem.denormalize_info; eauto. i. des. subst. 
          assert (INBLK1: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (Int64.unsigned i1) b0).
          { eapply Mem.conditions_of_addr_in_block; eauto. }
          exploit Mem.valid_pointer_implies; try eapply VLD2. i.
          eapply weak_valid_concrete_extends in H; eauto.
          exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|].
          i. des. subst. inv INRANGE. simpl in *.
          assert (INBLK2: Mem.addr_in_block (Mem.mem_concrete m') (Mem.mem_access m') (caddr0 + Ptrofs.unsigned i0) b1).
          { eapply Mem.conditions_of_addr_in_block; eauto.
            - replace (caddr0 + Ptrofs.unsigned i0 - caddr0) with (Ptrofs.unsigned i0) by lia.
              eapply SAMEVLD in VLD2. rewrite Mem.valid_pointer_nonempty_perm in VLD2; eauto.
              eapply Mem.perm_cur_max. eauto.
            - replace (caddr0 + Ptrofs.unsigned i0 - caddr0) with (Ptrofs.unsigned i0) by lia.
              eapply Ptrofs.unsigned_range_2. }
          assert (INBLK1': Mem.addr_in_block (Mem.mem_concrete m') (Mem.mem_access m') (Int64.unsigned i1) b0).
          { inv INBLK1. econs; eauto; [eapply extended_concrete; eauto|].
            des. exploit extended_access; eauto. i. unfold Mem.perm, Mem.perm_order' in H0.
            des_ifs; eauto. }
          exploit Ptrofs.modulus_eq64; eauto. i.
          assert (Int64.eq i1 (Int64.repr (caddr0 + Ptrofs.unsigned i0)) = false).
          { unfold Int64.eq. rewrite Int64.unsigned_repr.
            2:{ unfold Int64.max_unsigned. rewrite <- H0. lia. }
            destruct (zeq (Int64.unsigned i1) (caddr0 + Ptrofs.unsigned i0)) eqn:ZEQ;[|eauto].
            { rewrite <- e in INBLK2. exfalso. eapply n. eapply Mem.no_concrete_overlap; eauto. } }
          rewrite NULL1, BIT. destruct c; simpl in *; inv H1; right; rewrite H3; eauto. }
    + inversion TOPTR1; subst.
      destruct v2; simpl in *; [clarify|clarify|rewrite BIT in *; simpl in *; clarify|clarify|clarify|simpl in *].
      * destruct (Int64.eq i1 Int64.zero) eqn:NULL1; simpl in *; [clarify| ].
        destruct (Mem.denormalize (Int64.unsigned i1) m) eqn:DENO2; [|simpl in *; clarify].
        destruct p. simpl in TOPTR2. simpl in *. inv TOPTR2. inv BIND2. inv BIND1;[|clarify|].
        { left. exploit denormalize_concrete_extends; eauto. i. des. unfold Mem.to_ptr. rewrite BIT, H, NULL1. simpl.
          rewrite BIT. eapply andb_prop in VLD. des. eapply valid_concrete_extends in VLD, VLD0; eauto.
          destruct (eq_block b0 b1); [subst; clarify|]. rewrite VLD, VLD0. eauto. }
        { simpl. eapply andb_prop in VLD. destruct VLD as [VLD1 VLD2]. simpl in H4. unfold Mem.ptr2int_v in H4.
          destruct (Mem.ptr2int b0 (Ptrofs.unsigned i) m') eqn:P2I; cycle 1;[inv H4|].
          rewrite BIT in H4. inv H4. exploit Mem.denormalize_info; eauto. i. des. subst.
          assert (INBLK1: Mem.addr_in_block (Mem.mem_concrete m) (Mem.mem_access m) (Int64.unsigned i1) b1).
          { eapply Mem.conditions_of_addr_in_block; eauto. }
          exploit Mem.valid_pointer_implies; try eapply VLD1. i.
          eapply weak_valid_concrete_extends in H; eauto.
          exploit Mem.ptr2int_weak_valid'; eauto; [eapply Ptrofs.unsigned_range_2|].
          i. des. subst. inv INRANGE. simpl in *.
          assert (INBLK2: Mem.addr_in_block (Mem.mem_concrete m') (Mem.mem_access m') (caddr0 + Ptrofs.unsigned i) b0).
          { eapply Mem.conditions_of_addr_in_block; eauto.
            - replace (caddr0 + Ptrofs.unsigned i - caddr0) with (Ptrofs.unsigned i) by lia.
              eapply SAMEVLD in VLD1. rewrite Mem.valid_pointer_nonempty_perm in VLD1; eauto.
              eapply Mem.perm_cur_max. eauto.
            - replace (caddr0 + Ptrofs.unsigned i - caddr0) with (Ptrofs.unsigned i) by lia.
              eapply Ptrofs.unsigned_range_2. }
          assert (INBLK1': Mem.addr_in_block (Mem.mem_concrete m') (Mem.mem_access m') (Int64.unsigned i1) b1).
          { inv INBLK1. econs; eauto; [eapply extended_concrete; eauto|].
            des. exploit extended_access; eauto. i. unfold Mem.perm, Mem.perm_order' in H0.
            des_ifs; eauto. }
          exploit Ptrofs.modulus_eq64; eauto. i.
          assert (Int64.eq (Int64.repr (caddr0 + Ptrofs.unsigned i)) i1 = false).
          { unfold Int64.eq. rewrite Int64.unsigned_repr.
            2:{ unfold Int64.max_unsigned. rewrite <- H0. lia. }
            destruct (zeq (caddr0 + Ptrofs.unsigned i) (Int64.unsigned i1)) eqn:ZEQ;[|eauto].
            { rewrite e in INBLK2. exfalso. eapply n. eapply Mem.no_concrete_overlap; eauto. } }
          destruct c; simpl in *; inv H1; right; rewrite H3; eauto. }
      * inv TOPTR2. eapply andb_prop in VLD. destruct VLD as [VLD1 VLD2].
        inv BIND1; [ | clarify | ].
        { inv BIND2; [ | clarify | ].
          - simpl. rewrite BIT. destruct (eq_block b0 b1); [subst;clarify|].
            eapply SAMEVLD in VLD1, VLD2. rewrite VLD1, VLD2. simpl. eauto.
          - simpl in H4. unfold Mem.ptr2int_v in H4.
            destruct (Mem.ptr2int b1 (Ptrofs.unsigned i0) m') eqn:P2I; [|inv H4].
            rewrite BIT in *. inv H4. exploit Mem.ptr2int_to_denormalize; eauto.
            { eapply Ptrofs.unsigned_range_2. }
            i. des. exploit Mem.denormalize_paddr_in_range; eauto.  i. inv H0.
            unfold fst, snd in *.
            left. simpl. rewrite BIT. simpl. rewrite Int64.unsigned_repr.
            2:{ unfold Int64.max_unsigned. rewrite <- Ptrofs.modulus_eq64; eauto. lia. }
            exploit Mem.denormalized_not_nullptr64; eauto. i. rewrite H0.
            rewrite H. simpl. destruct (eq_block b0 b1); [subst; clarify|].
            eapply SAMEVLD in VLD1, VLD2. rewrite Ptrofs.repr_unsigned. simpl. rewrite VLD1, VLD2. eauto. }
        { inv BIND2; [ | clarify | ].
          - simpl in H4. unfold Mem.ptr2int_v in H4.
            destruct (Mem.ptr2int b0 (Ptrofs.unsigned i) m') eqn:P2I; [|inv H4].
            rewrite BIT in *. inv H4. exploit Mem.ptr2int_to_denormalize; eauto.
            { eapply Ptrofs.unsigned_range_2. }
            i. des. exploit Mem.denormalize_paddr_in_range; eauto. i. inv H0.
            unfold fst, snd in *.
            left. simpl. rewrite BIT. simpl. rewrite Int64.unsigned_repr.
            2:{ unfold Int64.max_unsigned. rewrite <- Ptrofs.modulus_eq64; eauto. lia. }
            exploit Mem.denormalized_not_nullptr64; eauto. i. rewrite H0.
            rewrite H. simpl. destruct (eq_block b0 b1); [subst; clarify|].
            eapply SAMEVLD in VLD1, VLD2. rewrite Ptrofs.repr_unsigned. rewrite VLD1, VLD2.
            rewrite BIT. eauto.
          - simpl in H4, H6. unfold Mem.ptr2int_v in H4, H6.
            destruct (Mem.ptr2int b0 (Ptrofs.unsigned i) m') eqn:P2I; [|inv H4].
            destruct (Mem.ptr2int b1 (Ptrofs.unsigned i0) m') eqn:P2I'; [|inv H6].
            rewrite BIT in *. inv H4; inv H6.
            exploit Mem.ptr2int_to_denormalize; try eapply P2I; eauto; i.
            { eapply Ptrofs.unsigned_range_2. }
            exploit Mem.ptr2int_to_denormalize; try eapply P2I'; eauto; i; des.
            { eapply Ptrofs.unsigned_range_2. }
            exploit Mem.denormalize_paddr_in_range; try eapply H; eauto. i. inv H4.
            exploit Mem.denormalize_paddr_in_range; try eapply H0; eauto. i. inv H4.
            unfold fst, snd in *. left. simpl. rewrite BIT. simpl.
            exploit Mem.denormalized_not_nullptr64; try eapply H; eauto. i.
            exploit Mem.denormalized_not_nullptr64; try eapply H0; eauto. i. des.
            rewrite H4, H5. rewrite Int64.unsigned_repr.
            2:{ unfold Int64.max_unsigned. rewrite <- Ptrofs.modulus_eq64; eauto. lia. }
            rewrite Int64.unsigned_repr.
            2:{ unfold Int64.max_unsigned. rewrite <- Ptrofs.modulus_eq64; eauto. lia. }
            rewrite H, H0. simpl. rewrite BIT. destruct (eq_block b0 b1); [subst; clarify|].
            eapply SAMEVLD in VLD1, VLD2. do 2 rewrite Ptrofs.repr_unsigned. rewrite VLD1, VLD2. eauto. }
Qed.

Lemma cmplu_bool_to_int_binded
    m m' v1 v1' v2 v2' c b
    (CONCEXT: concrete_extends m m')
    (BIND1: val_intptr m' v1 v1')
    (BIND2: val_intptr m' v2 v2')
    (CMP: Val.cmplu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2) = Some b) :
  <<CMPI: Val.cmplu_bool (Mem.valid_pointer m') c (to_int_val m' v1') (to_int_val m' v2') = Some b>>.
Proof.
  destruct Archi.ptr64 eqn:BIT.
  2: { unfold Val.cmplu_bool in CMP. rewrite BIT in *; des_ifs
       ;unfold to_int_val, Mem.to_int in Heq, Heq0; des_ifs; simpl in *; clarify; des_ifs;
       inv BIND1; inv BIND2; simpl; eauto. }
  unfold Val.cmplu_bool in CMP. rewrite BIT in CMP.
  destruct (to_int_val m v1) eqn:TOINT1; inversion CMP.
  2:{ eapply to_int_val_int_or_undef in TOINT1. des; clarify. }
  destruct (to_int_val m v2) eqn:TOINT2; inversion CMP.
  2:{ eapply to_int_val_int_or_undef in TOINT2. des; clarify. }
  exploit to_int_bind; try eapply BIND1; eauto. intros IBIND1.
  exploit to_int_bind; try eapply BIND2; eauto. intros IBIND2. des.
  rewrite TOINT1 in IBIND1. rewrite TOINT2 in IBIND2. inv IBIND1; inv IBIND2.
  simpl. eauto.
Qed.

Lemma cmpu_join_binded
    v1 v1' v2 v2' c m m' b
    (BIND1: val_intptr m' v1 v1')
    (BIND2: val_intptr m' v2 v2')
    (CONCEXT: concrete_extends m m')
    (CMP: cmpu_join m c v1 v2 = Some b) :
  <<CMP: cmpu_join m' c v1' v2' = Some b>>.
Proof.
  unfold cmpu_join in *.
  destruct (Val.cmpu_bool (Mem.valid_pointer m) c (to_ptr_val m v1) (to_ptr_val m v2)) eqn:PCMP.
  - exploit cmpu_bool_to_ptr_binded; try eapply PCMP; eauto. intros [PCMP'|ICMP'].
    + destruct (Val.cmpu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2)) eqn:ICMP.
      { exploit cmpu_bool_to_int_binded; try eapply ICMP; eauto. i. rewrite PCMP', H. eauto. }
      destruct (Val.cmpu_bool (Mem.valid_pointer m') c (to_int_val m' v1') (to_int_val m' v2')) eqn:ICMP'.
      { exploit cmpu_no_angelic; try eapply ICMP'; eauto. i. des; subst. rewrite PCMP'.
        ss. inv CMP. eapply bool_join_angelic; eauto. }
      rewrite PCMP'. simpl in *. eauto.
    + destruct (Val.cmpu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2)) eqn:ICMP.
      { exploit cmpu_no_angelic; try eapply PCMP; eauto. i. des; subst.
        destruct (Val.cmpu_bool (Mem.valid_pointer m') c (to_ptr_val m' v1') (to_ptr_val m' v2')) eqn:PCMP'.
        { exploit cmpu_no_angelic; try eapply PCMP'; eauto. i. des; subst. rewrite ICMP'. eauto. }
        rewrite ICMP'. simpl in *. rewrite bool_join_angelic in CMP; eauto. }
      destruct (Val.cmpu_bool (Mem.valid_pointer m') c (to_ptr_val m' v1') (to_ptr_val m' v2')) eqn:PCMP'.
      { exploit cmpu_no_angelic; try eapply PCMP'; eauto. i. des; subst. rewrite ICMP'. ss.
        rewrite bool_join_angelic; eauto. }
      rewrite ICMP'. eauto.
  - destruct (Val.cmpu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2)) eqn:ICMP.
    2:{ simpl in CMP. inv CMP. }
    exploit cmpu_bool_to_int_binded; try eapply ICMP; eauto. i. rewrite H.
    destruct (Val.cmpu_bool (Mem.valid_pointer m') c (to_ptr_val m' v1') (to_ptr_val m' v2')) eqn:PCMP'; eauto.
    { exploit cmpu_no_angelic; try eapply PCMP'; eauto. i. des; subst. ss. rewrite bool_join_angelic; eauto. }
Qed.

Lemma cmplu_join_binded
    v1 v1' v2 v2' c m m' b
    (BIND1: val_intptr m' v1 v1')
    (BIND2: val_intptr m' v2 v2')
    (CONCEXT: concrete_extends m m')
    (CMP: cmplu_join m c v1 v2 = Some b) :
  <<CMP: cmplu_join m' c v1' v2' = Some b>>.
Proof.
  unfold cmplu_join in *.
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_ptr_val m v1) (to_ptr_val m v2)) eqn:PCMP.
  - exploit cmplu_bool_to_ptr_binded; try eapply PCMP; eauto. intros [PCMP'|ICMP'].
    + destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2)) eqn:ICMP.
      { exploit cmplu_bool_to_int_binded; try eapply ICMP; eauto. i. rewrite PCMP', H. eauto. }
      destruct (Val.cmplu_bool (Mem.valid_pointer m') c (to_int_val m' v1') (to_int_val m' v2')) eqn:ICMP'.
      { exploit cmplu_no_angelic; try eapply ICMP'; eauto. i. des; subst. rewrite PCMP'.
        ss. inv CMP. eapply bool_join_angelic; eauto. }
      rewrite PCMP'. simpl in *. eauto.
    + destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2)) eqn:ICMP.
      { exploit cmplu_no_angelic; try eapply PCMP; eauto. i. des; subst.
        destruct (Val.cmplu_bool (Mem.valid_pointer m') c (to_ptr_val m' v1') (to_ptr_val m' v2')) eqn:PCMP'.
        { exploit cmplu_no_angelic; try eapply PCMP'; eauto. i. des; subst. rewrite ICMP'. eauto. }
        rewrite ICMP'. simpl in *. rewrite bool_join_angelic in CMP; eauto. }
      destruct (Val.cmplu_bool (Mem.valid_pointer m') c (to_ptr_val m' v1') (to_ptr_val m' v2')) eqn:PCMP'.
      { exploit cmplu_no_angelic; try eapply PCMP'; eauto. i. des; subst. rewrite ICMP'. ss.
        rewrite bool_join_angelic; eauto. }
      rewrite ICMP'. eauto.
  - destruct (Val.cmplu_bool (Mem.valid_pointer m) c (to_int_val m v1) (to_int_val m v2)) eqn:ICMP.
    2:{ simpl in CMP. inv CMP. }
    exploit cmplu_bool_to_int_binded; try eapply ICMP; eauto. i. rewrite H.
    destruct (Val.cmplu_bool (Mem.valid_pointer m') c (to_ptr_val m' v1') (to_ptr_val m' v2')) eqn:PCMP'; eauto.
    { exploit cmplu_no_angelic; try eapply PCMP'; eauto. i. des; subst. ss. rewrite bool_join_angelic; eauto. }
Qed.

Lemma cmplu_bool_ptr_concrete_extends
    c m m' b1 b2 ofs1 ofs2 b
    (SF: Archi.ptr64 = true)
    (CONCEXT: concrete_extends m m')
    (CMP: Val.cmplu_bool (Mem.valid_pointer m) c (Vptr b1 ofs1) (Vptr b2 ofs2) = Some b):
  Val.cmplu_bool (Mem.valid_pointer m') c (Vptr b1 ofs1) (Vptr b2 ofs2) = Some b.
Proof.
  assert (SAMEVLD: forall b ofs, Mem.valid_pointer m b ofs = true -> Mem.valid_pointer m' b ofs = true).
  { eapply valid_concrete_extends; eauto. }
  assert (SAMEWVLD: forall b ofs, Mem.weak_valid_pointer m b ofs = true -> Mem.weak_valid_pointer m' b ofs = true).
  { eapply weak_valid_concrete_extends; eauto. }
  unfold Val.cmplu_bool in CMP. rewrite SF in CMP. simpl in CMP.
  fold (Mem.weak_valid_pointer m b1 (Ptrofs.unsigned ofs1)) in *.
  fold (Mem.weak_valid_pointer m b2 (Ptrofs.unsigned ofs2)) in *.
  destruct (eq_block b1 b2); subst.
  - destruct (Mem.weak_valid_pointer m b2 (Ptrofs.unsigned ofs1) &&
                Mem.weak_valid_pointer m b2 (Ptrofs.unsigned ofs2)) eqn:WVLD; [|inv CMP].
    eapply andb_prop in WVLD. des_safe. eapply SAMEWVLD in WVLD, WVLD0.
    simpl. unfold Mem.weak_valid_pointer in WVLD, WVLD0. rewrite SF, WVLD, WVLD0. simpl. des_ifs.
  - destruct (Mem.valid_pointer m b1 (Ptrofs.unsigned ofs1) &&
                Mem.valid_pointer m b2 (Ptrofs.unsigned ofs2)) eqn:VLD; [|inv CMP].
    eapply andb_prop in VLD. des_safe. eapply SAMEVLD in VLD, VLD0.
    simpl. rewrite SF, VLD, VLD0. simpl. des_ifs.
Qed.

Lemma cmplu_bool_ptr_binded
  c m m' b1 b2 ofs1 ofs2 v1' v2' b
  (CONCEXT: concrete_extends m m')
  (BIND1: val_intptr m' (Vptr b1 ofs1) v1')
  (BIND2: val_intptr m' (Vptr b2 ofs2) v2')
  (CMP: Val.cmplu_bool (Mem.valid_pointer m) c (Vptr b1 ofs1) (Vptr b2 ofs2) = Some b) :
  <<CMP: eval_condition_join (Ccomplu c) [v1'; v2'] m' = Some b>>.
Proof.
  assert (SAMEVLD: forall b ofs, Mem.valid_pointer m b ofs = true -> Mem.valid_pointer m' b ofs = true).
  { eapply valid_concrete_extends; eauto. }
  assert (SAMEWVLD: forall b ofs, Mem.weak_valid_pointer m b ofs = true -> Mem.weak_valid_pointer m' b ofs = true).
  { eapply weak_valid_concrete_extends; eauto. }
  exploit cmplu_bool_to_ptr_binded. eauto. eapply BIND1. eapply BIND2.
  { eauto. }
  i. simpl. destruct Archi.ptr64 eqn:SF.
  2:{ inv BIND1; inv BIND2; clarify. }
  inv BIND1; inv BIND2; try rewrite SF in *; clarify.
  - eapply cmplu_bool_ptr_concrete_extends; eauto.
  - unfold cmplu_join_common. simpl in H4. unfold Mem.ptr2int_v in H4. des_ifs_safe.
    exploit Mem.ptr2int_not_nullptr64; eauto.
    { unfold Val.cmplu_bool in CMP. des_ifs.
      - eapply andb_prop in Heq1. des_safe. eapply SAMEWVLD. unfold Mem.weak_valid_pointer. eauto.
      - eapply andb_prop in Heq1. des_safe. eapply SAMEWVLD. unfold Mem.weak_valid_pointer.
        rewrite Heq2. eauto. }
    { eapply Ptrofs.unsigned_range_2. }
    i. rewrite H0. unfold cmplu_join. des.
    + rewrite CMPP. unfold bool_optjoin. simpl. des_ifs.
      exploit cmplu_no_angelic; eauto. i. eapply bool_join_angelic; eauto.
    + rewrite CMPI. unfold bool_optjoin.
      destruct (Val.cmplu_bool (Mem.valid_pointer m') c (to_ptr_val m' (Vptr b1 ofs1))
                  (to_ptr_val m' (Vlong (Int64.repr z)))) eqn:PCMP; eauto.
      exploit cmplu_no_angelic; eauto. i. rewrite H. eapply bool_join_angelic; eauto.
  - unfold cmplu_join_common. simpl in H4. unfold Mem.ptr2int_v in H4. des_ifs_safe.
    exploit Mem.ptr2int_not_nullptr64; eauto;[|eapply Ptrofs.unsigned_range_2|].
    { unfold Val.cmplu_bool in CMP. des_ifs.
      - eapply andb_prop in Heq1. des_safe. eapply SAMEWVLD. unfold Mem.weak_valid_pointer. eauto.
      - eapply andb_prop in Heq1. des_safe. eapply SAMEWVLD. unfold Mem.weak_valid_pointer.
        rewrite Heq1. eauto. }
    i. rewrite H0. unfold cmplu_join. des.
    + rewrite CMPP. unfold bool_optjoin.
      destruct (Val.cmplu_bool (Mem.valid_pointer m') c (to_int_val m' (Vlong (Int64.repr z)))
                                                        (to_int_val m' (Vptr b2 ofs2))) eqn:CMPI; eauto.
      exploit cmplu_no_angelic; eauto. i. eapply bool_join_angelic; eauto.
    + rewrite CMPI. unfold bool_optjoin.
      destruct (Val.cmplu_bool (Mem.valid_pointer m') c (to_ptr_val m' (Vlong (Int64.repr z)))
                                                        (to_ptr_val m' (Vptr b2 ofs2))) eqn:CMPP; eauto.
      exploit cmplu_no_angelic; eauto. i. rewrite H. eapply bool_join_angelic; eauto.
  - des; eauto. destruct (Val.cmplu_bool (Mem.valid_pointer m') c (Vlong i) (Vlong i0)) eqn:CMPI.
    2:{ simpl in CMPI. clarify. }
    unfold Mem.to_int, Mem.ptr2int_v in *. des_ifs.
    exploit (cmplu_no_angelic m' c (Vptr b1 ofs1) (Vptr b2 ofs2)).
    { eapply cmplu_bool_ptr_concrete_extends; eauto. }
    { unfold to_int_val. simpl. rewrite Heq, Heq0, SF. eauto. }
    i. rewrite H; eauto.
Qed.

Lemma cmplu_bool_null_binded_l
    c m m' n b1 ofs1 v1' v2' b
    (CONCEXT: concrete_extends m m')
    (BIND1: val_intptr m' (Vlong n) v1')
    (BIND2: val_intptr m' (Vptr b1 ofs1) v2')
    (CMP: Val.cmplu_bool (Mem.valid_pointer m) c (Vlong n) (Vptr b1 ofs1) = Some b) :
  <<CMP: eval_condition_join (Ccomplu c) [v1'; v2'] m' = Some b>>.
Proof.
  assert (SAMEVLD: forall b ofs, Mem.valid_pointer m b ofs = true -> Mem.valid_pointer m' b ofs = true).
  { eapply valid_concrete_extends; eauto. }
  unfold Val.cmplu_bool in CMP. des_ifs.
  eapply andb_prop in Heq0. des. inv BIND1; inv BIND2; [|clarify|].
  - ss. des_ifs_safe. rewrite andb_false_iff in Heq2. des; clarify.
    exploit weak_valid_concrete_extends; eauto. i. eapply orb_prop in H.
    des; clarify. erewrite orb_true_r in Heq2. clarify.
  - ss. des_ifs. exploit Mem.ptr2int_weak_valid'; eauto.
    { eapply weak_valid_concrete_extends; eauto. }
    { eapply Ptrofs.unsigned_range_2. }
    i. des. inv INRANGE. simpl in *.
    assert (EQ: Int64.eq Int64.zero (Int64.repr (caddr + Ptrofs.unsigned ofs1)) = false).
    { unfold Int64.eq. rewrite Int64.unsigned_repr.
      2:{ rewrite Ptrofs.modulus_eq64 in SND; eauto. unfold Int64.max_unsigned. lia. }
      rewrite Int64.unsigned_zero. des_ifs; lia. }
    eapply Int64.same_if_eq in Heq0; subst.
    destruct c; ss; inv CMP; rewrite EQ; eauto.
Qed.

Lemma cmplu_bool_null_binded_r
    c m m' n b1 ofs1 v1' v2' b
    (CONCEXT: concrete_extends m m')
    (BIND1: val_intptr m' (Vptr b1 ofs1) v1')
    (BIND2: val_intptr m' (Vlong n) v2')
    (CMP: Val.cmplu_bool (Mem.valid_pointer m) c (Vptr b1 ofs1) (Vlong n) = Some b) :
  <<CMP: eval_condition_join (Ccomplu c) [v1'; v2'] m' = Some b>>.
Proof.
  assert (SAMEVLD: forall b ofs, Mem.valid_pointer m b ofs = true -> Mem.valid_pointer m' b ofs = true).
  { eapply valid_concrete_extends; eauto. }
  unfold Val.cmplu_bool in CMP. des_ifs.
  eapply andb_prop in Heq0. des. inv BIND1; inv BIND2; [|clarify|].
  - ss. des_ifs_safe. rewrite andb_false_iff in Heq2. des; clarify.
    exploit weak_valid_concrete_extends; eauto. i. eapply orb_prop in H.
    des; clarify. erewrite orb_true_r in Heq2. clarify.
  - ss. des_ifs. exploit Mem.ptr2int_weak_valid'; eauto.
    { eapply weak_valid_concrete_extends; eauto. }
    { eapply Ptrofs.unsigned_range_2. }
    i. des. inv INRANGE. simpl in *.
    assert (EQ: Int64.eq Int64.zero (Int64.repr (caddr + Ptrofs.unsigned ofs1)) = false).
    { unfold Int64.eq. rewrite Int64.unsigned_repr.
      2:{ rewrite Ptrofs.modulus_eq64 in SND; eauto. unfold Int64.max_unsigned. lia. }
      rewrite Int64.unsigned_zero. des_ifs; lia. }
    eapply Int64.same_if_eq in Heq0; subst.
    destruct c; ss; inv CMP; rewrite Int64.eq_sym; rewrite EQ; eauto.
Qed.

Lemma cmplu_bool_long_binded
    c m m' n1 n2 v1' v2' b
    (CONCEXT: concrete_extends m m')
    (BIND1: val_intptr m' (Vlong n1) v1')
    (BIND2: val_intptr m' (Vlong n2) v2')
    (CMP: Val.cmplu_bool (Mem.valid_pointer m) c (Vlong n1) (Vlong n2) = Some b) :
  <<CMP: eval_condition_join (Ccomplu c) [v1'; v2'] m' = Some b>>.
Proof. inv BIND1; inv BIND2. simpl in *. eauto. Qed.

Lemma eval_condition_join_binded
    c m m' vl vl' b
    (COND: ptr_cond c = true)
    (CONCEXT: concrete_extends m m')
    (BIND: val_intptrist m' vl vl')
    (EVAL: eval_condition_join c vl m = Some b) :
  <<EVAL: eval_condition_join c vl' m' = Some b>>.
Proof.
  assert (SAMEVLD: forall b ofs, Mem.valid_pointer m b ofs = true -> Mem.valid_pointer m' b ofs = true).
  { eapply valid_concrete_extends; eauto. }
  assert (SAMEWVLD: forall b ofs, Mem.weak_valid_pointer m b ofs = true -> Mem.weak_valid_pointer m' b ofs = true).
  { eapply weak_valid_concrete_extends; eauto. }
  destruct (Archi.ptr64) eqn:BIT;[|ss].
  - destruct c eqn: CC; simpl in *; try rewrite BIT in *; inv COND.
    2:{ unfold cmplu_join_common in *. destruct BIND; [ss|]. destruct BIND; [|ss]. dup H.
        destruct v1; try by inv EVAL.
        - inv H. simpl in *. eauto.
        - destruct (Int64.eq n Int64.zero) eqn:NULL.
          + exploit cmplu_bool_null_binded_r; try eapply EVAL; eauto. econs. i.
            ss. unfold cmplu_join_common in *. rewrite NULL in H1. eauto.
          + inv H0;[|clarify|].
            { eapply cmplu_join_binded; eauto. econs. }
            { exploit cmplu_join_binded.
              eauto. instantiate (1:=Vlong n). econs 2. eauto. eauto. i.
              r in H0. unfold cmplu_join in H0. ss.
              destruct (Val.cmplu_bool (Mem.valid_pointer m') c0 (to_ptr_val m' (Vlong i0))
                                                                 (to_ptr_val m' (Vlong n))) eqn:PCMP; ss.
              { exploit cmplu_no_angelic; eauto; ss. i. r in H1.
                subst. rewrite bool_join_angelic in H0; eauto. } } }
    unfold cmplu_join_common in *. do 2 (destruct BIND; [ss|]). destruct BIND; [|ss].
    fold eval_condition_join. destruct v1, v0; try (by ss).
    + inv H; inv H0. ss.
    + destruct (Int64.eq i Int64.zero) eqn:NULL.
      { inv H; inv H0;[|clarify|].
        - ss. rewrite NULL, BIT in *. ss.
          fold (Mem.weak_valid_pointer m b0 (Ptrofs.unsigned i0)) in *.
          destruct (Mem.weak_valid_pointer m b0 (Ptrofs.unsigned i0)) eqn:WVLD; [|inv EVAL].
          eapply SAMEWVLD in WVLD. unfold Mem.weak_valid_pointer in WVLD. rewrite WVLD. eauto.
        - exploit cmplu_bool_null_binded_l; eauto. econs. econs 7; eauto. i. ss. }
      { exploit cmplu_join_binded; try eapply EVAL; eauto. i. inv H; inv H0;[|clarify|].
        - rewrite NULL. eauto.
        - unfold cmplu_join in H1. simpl in H1.
          destruct (Val.cmplu_bool (Mem.valid_pointer m') c0 (to_ptr_val m' (Vlong i)) (to_ptr_val m' (Vlong i1))) eqn:PCMP; ss.
          { simpl in *. exploit cmplu_no_angelic; eauto; ss. i. r in H. subst.
            rewrite bool_join_angelic in H1; eauto. } }
    + inv H; inv H0;[|clarify|].
      * destruct (Int64.eq i0 Int64.zero) eqn:NULL.
        { ss. rewrite NULL, BIT in *. ss.
          fold (Mem.weak_valid_pointer m b0 (Ptrofs.unsigned i)) in *.
          destruct (Mem.weak_valid_pointer m b0 (Ptrofs.unsigned i)) eqn:WVLD; [|inv EVAL].
          eapply SAMEWVLD in WVLD. unfold Mem.weak_valid_pointer in WVLD. rewrite WVLD. eauto. }
        { eapply cmplu_join_binded; eauto; econs. }
      * destruct (Int64.eq i0 Int64.zero) eqn:NULL.
        { exploit cmplu_bool_null_binded_r; eauto. econs 7; eauto. econs. i. ss. }
        { exploit cmplu_join_binded; eauto. econs 7; eauto. econs. i.
          r in H. unfold cmplu_join in H. ss.
          destruct (Val.cmplu_bool (Mem.valid_pointer m') c0 (to_ptr_val m' (Vlong i1))
                      (to_ptr_val m' (Vlong i0))) eqn:PCMP; ss.
          { simpl in *. exploit cmplu_no_angelic; eauto; ss. i. r in H0. subst.
            rewrite bool_join_angelic in H; eauto. } }
    + eapply cmplu_bool_ptr_binded; eauto.
Qed.

Lemma eval_operation_join_eval_condition_join op c sp vl m
    (OPCOND: op = Ocmp c)
    (COND: ptr_cond c = true) :
  eval_operation_join genv sp op vl m = Some (Val.of_optbool (eval_condition_join c vl m)).
Proof.
  subst. unfold eval_operation_join, eval_operation, eval_condition_join in *.
  unfold Val.of_optbool, Vtrue, Vfalse.
  destruct (eval_condition c (map (to_ptr_val m) vl) m) eqn:PCMP; simpl.
  - destruct (eval_condition c (map (to_int_val m) vl) m) eqn:ICMP; simpl.
    + des_ifs; clarify.
    + unfold val_join. des_ifs.
  - destruct (eval_condition c (map (to_int_val m) vl) m) eqn:ICMP; eauto.
Qed.

Lemma psubl_join_binded
    m m' v1 v2 v1' v2' v
    (CONCEXT: concrete_extends m m')
    (BIND1: val_intptr m' v1 v1')
    (BIND2: val_intptr m' v2 v2')
    (PSUB: psubl_join m v1 v2 = v) :
  exists v', <<PSUB: psubl_join m' v1' v2' = v'>> /\ <<BIND: val_intptr m' v v'>>.
Proof.
  unfold psubl_join in *.
  specialize (psubl_only_long_and_undef (to_ptr_val m v1) (to_ptr_val m v2)).
  specialize (psubl_only_long_and_undef (to_int_val m v1) (to_int_val m v2)). i.
  destruct (Val.psubl (to_ptr_val m v1) (to_ptr_val m v2)) eqn:PSUB1; des; inv H;
  destruct (Val.psubl (to_int_val m v1) (to_int_val m v2)) eqn:PSUB2; des; inv H0;
  simpl; esplits; eauto; try econs; inv H2.
  - exploit psubl_to_int_binded; try eapply PSUB2; eauto. i. des. subst. inv H0.
    symmetry in H. erewrite val_join_angelic_vi; eauto; [econs| |ii; clarify].
    { eapply psubl_wrapper_no_angelic; eauto. }
  - exploit psubl_to_ptr_binded; try eapply PSUB1; eauto. i. des.
    + inv PSUBP0. symmetry in H1. rewrite H1. erewrite val_join_angelic_vp; eauto; [econs| |ii; clarify].
      { eapply psubl_wrapper_no_angelic; eauto. }
    + inv PSUBI0. symmetry in H1. rewrite H1. erewrite val_join_angelic_vi; eauto; [econs| |ii; clarify].
      { eapply psubl_wrapper_no_angelic; eauto. }
  - exploit psubl_wrapper_no_angelic; eauto. i. des; subst; inv H.
    rewrite Int64.eq_true. exploit psubl_to_int_binded; try eapply PSUB2; eauto. i. des. subst. inv H0.
    symmetry in H. erewrite val_join_angelic_vi; eauto; [econs| |ii; clarify].
    { eapply psubl_wrapper_no_angelic; eauto. }
Qed.

Lemma eval_operation_join_binded
    m m' vl vl' sp op v
    (PTRBIN: ptr_binop op = true)
    (CONCEXT: concrete_extends m m')
    (BIND: val_intptrist m' vl vl')
    (EVAL: eval_operation_join genv sp op vl m = Some v) :
  exists v', <<EVAL2: eval_operation_join genv sp op vl' m' = Some v'>>
      /\ <<VIND': val_intptr m' v v'>>.
Proof.
  destruct (Archi.ptr64) eqn:BIT; [|ss].
  - destruct op; ss.
    (* psubl p >= i *)
    + do 2 (destruct BIND; [inv EVAL|]). destruct BIND; [|inv EVAL].
      rewrite BIT in *. destruct v1, v0; try by (simpl in *; inv EVAL; des_ifs; esplits; eauto; econs).
      (* * inv EVAL. des_ifs; esplits; econs; eauto. *)
      * inv H; inv H0. esplits; eauto. simpl. eapply val_intptr_refl.
      * dup H. dup H0. exploit psubl_join_binded. eauto. eapply H. eapply H0. inv EVAL; eauto.
        i. des. subst. inv H; inv H0;[|clarify|].
        { inv EVAL. esplits; eauto. }
        { inv EVAL. esplits; eauto. unfold psubl_join in BIND.
          erewrite (val_join_angelic_vi _ (Val.psubl (to_int_val m' (Vlong i)) (to_int_val m' (Vlong i1)))) in BIND; eauto.
          { eapply psubl_wrapper_no_angelic; eauto. }
          { ii. simpl in H. clarify. } }
      * dup H. dup H0. exploit psubl_join_binded. eauto. eapply H. eapply H0. inv EVAL; eauto.
        i. des. subst. inv H; inv H0;[|clarify|].
        { inv EVAL. esplits; eauto. }
        { inv EVAL. esplits; eauto. unfold psubl_join in BIND.
          erewrite (val_join_angelic_vi _ (Val.psubl (to_int_val m' (Vlong i1)) (to_int_val m' (Vlong i0)))) in BIND; eauto.
          { eapply psubl_wrapper_no_angelic; eauto. }
          { ii. simpl in H. clarify. } }
      * destruct (classic (v = Vundef)).
        { subst. inv H; inv H0; ss; esplits; eauto; econs. }
        dup H. dup H0. exploit psubl_join_binded. eauto. eapply H. eapply H0.
        { instantiate (1:= v). unfold psubl_join. rewrite val_join_angelic_vp.
          - simpl. inv EVAL. eauto.
          - ss. des_ifs.
          - eapply psubl_wrapper_no_angelic; eauto.
          - ii. ss. clarify. }
        i. des; subst. inv H; inv H0; ss;[|esplits; eauto|esplits; eauto|].
        { inv EVAL. esplits; eauto. eapply val_intptr_refl. }
        { rewrite BIT.  unfold psubl_join in BIND. rewrite val_join_angelic_vi in BIND; ss; eauto.
          eapply psubl_wrapper_no_angelic; eauto. }
    + destruct (eval_condition_join cond vl m) eqn:COND.
      2:{ ss. clarify. esplits; eauto. econs. }
      inv EVAL. exploit eval_condition_join_binded; eauto. i.
      rewrite H. ss. esplits; eauto. eapply val_intptr_refl.
Qed.

Lemma eval_operation_wrapper_binded
    m m' vl vl' sp op v
    (CONCEXT: concrete_extends m m')
    (BIND: val_intptrist m' vl vl')
    (EVAL: eval_operation_wrapper genv sp op vl m = Some v) :
  exists v', <<EVAL2: eval_operation_wrapper genv sp op vl' m' = Some v'>>
      /\ <<VIND': val_intptr m' v v'>>.
Proof.
  destruct (ptr_op op) eqn:PTROP; cycle 1.
  - unfold eval_operation_wrapper in *. rewrite PTROP in *.
    destruct op; simpl in EVAL; simpl; FuncInv; InvBind; TrivialExists;
      try (by (econs; eauto)); try (by (inv H2; ss; try econs)); try (by (inv H1; inv H2; ss; econs)).
    + eapply symbol_address_binded.
    + inv H1; inv H2; ss. des_ifs; clarify. esplits; eauto. econs.
    + inv H1; inv H2; ss. des_ifs; clarify. esplits; eauto. econs.
    + inv H1; inv H2; ss. des_ifs; clarify. esplits; eauto. econs.
    + inv H1; inv H2; ss. des_ifs; clarify. esplits; eauto. econs.
    + inv H1; inv H2; ss; try econs. des_ifs; econs; eauto.
    + inv H2; ss; try econs. des_ifs; econs; eauto.
    + inv H1; inv H2; ss; try econs. des_ifs; econs; eauto.
    + inv H2; ss; try econs. des_ifs; econs; eauto.
    + inv H1; ss; try discriminate. des_ifs. esplits; eauto. econs.
    + inv H1; inv H2; ss; try econs. des_ifs; clarify; econs.
    + inv H2; ss; try econs. des_ifs; econs; eauto.
    + inv H1; inv H2; ss; try econs; des_ifs; clarify; econs.
    + eapply eval_addressing32_binded; eauto.
    + eapply addl_bind; eauto. econs.
    + eapply subl_bind; eauto.
    + inv H1; inv H2; ss. des_ifs; clarify. esplits; eauto. econs.
    + inv H1; inv H2; ss. des_ifs; clarify. esplits; eauto. econs.
    + inv H1; inv H2; ss. des_ifs; clarify. esplits; eauto. econs.
    + inv H1; inv H2; ss. des_ifs; clarify. esplits; eauto. econs.
    + inv H1; inv H2; ss; try econs. des_ifs; econs; eauto.
    + inv H2; ss; try econs. des_ifs; econs; eauto.
    + inv H1; inv H2; ss; try econs. des_ifs; econs; eauto.
    + inv H2; ss; try econs. des_ifs; econs; eauto.
    + inv H1; ss; try discriminate. des_ifs. esplits; eauto. econs.
    + inv H1; inv H2; ss; try econs. des_ifs; clarify; econs.
    + inv H2; ss; try econs. des_ifs; econs; eauto.
    + eapply eval_addressing64_binded; eauto.
    + inv H1; simpl in EVAL; clarify. destruct (Float.to_int f) eqn:A; ss; clarify.
      exists (Vint i); auto. rewrite A. ss. esplits; eauto. econs.
    + inv H1; simpl in EVAL; clarify. esplits; ss; eauto. econs.
    + inv H1; simpl in EVAL; clarify. destruct (Float32.to_int f) eqn:A; ss; clarify.
      exists (Vint i); auto. rewrite A. ss. esplits; eauto. econs.
    + inv H1; simpl in EVAL; clarify. esplits; ss; eauto. econs.
    + inv H1; simpl in EVAL; clarify. destruct (Float.to_long f) eqn:A; ss; clarify.
      exists (Vlong i); auto. rewrite A. ss. esplits; eauto. econs.
    + inv H1; simpl in EVAL; clarify. esplits; ss; eauto. econs.
    + inv H1; simpl in EVAL; clarify. destruct (Float32.to_long f) eqn:A; ss; clarify.
      exists (Vlong i); auto. rewrite A. ss. esplits; eauto. econs.
    + inv H1; simpl in EVAL; clarify. esplits; ss; eauto. econs.
    + subst v. destruct (eval_condition cond vl m) eqn:?; cycle 1.
      { ss. econs. }
      exploit eval_condition_binded_no_ptr_binary; eauto. i. des.
      rewrite H. ss. eapply val_intptr_refl.
    + eapply select_binded; eauto. destruct (eval_condition c vl m) eqn:?; auto.
      right. symmetry. eapply eval_condition_binded_no_ptr_binary; eauto.
  (* ptr operations *)
  - destruct (Archi.ptr64) eqn:BIT.
    + destruct (ptr_binop op) eqn:PTRBINOP.
      (* ptr binop *)
      { unfold eval_operation_wrapper in *. rewrite PTROP in EVAL.
        assert (EVAL1: eval_operation_join genv sp op vl m = Some v) by (destruct op; ss).
        clear EVAL. exploit eval_operation_join_binded; eauto. i. des. rewrite EVAL2.
        esplits; eauto. rewrite PTROP. destruct op; simpl in *; clarify. }
      unfold ptr_op, ptr_cond in PTROP. (* rewrite BIT in *. *)
      destruct op; simpl in *; try rewrite BIT in *; inv PTROP; inv PTRBINOP.
      { rewrite H0 in H1. inv H1. }
      (* sel *)
      destruct c; simpl in *; inv H0.
      2:{ unfold eval_operation_wrapper in *.
          (* simpl in *. *) do 2 (destruct BIND;[inv EVAL|]).
          assert (PTRCMP: ptr_op (Osel (Ccompluimm c n) t) = true).
          { simpl. unfold ptr_cond. eapply orb_true_intro. left. simpl. eauto. }
          rewrite PTRCMP in *.
          destruct ((eval_condition_join (Ccompluimm c n) vl1 m)) eqn:COND1.
          2:{ simpl in EVAL. inv EVAL. esplits; eauto. econs. }
          exploit eval_condition_join_binded; eauto.
          i. rewrite H1. inv EVAL. simpl. esplits; eauto. simpl.
          eapply normalize_binded; eauto. destruct b; eauto. }
      unfold eval_operation_wrapper in *.
      (* simpl in *. *) do 2 (destruct BIND;[inv EVAL|]).
      assert (PTRCMP: ptr_op (Osel (Ccomplu c) t) = true).
      { simpl. unfold ptr_cond. eapply orb_true_intro. right. simpl. eauto. }
      rewrite PTRCMP in *.
      destruct ((eval_condition_join (Ccomplu c) vl1 m)) eqn:COND1.
      2:{ simpl in EVAL. inv EVAL. esplits; eauto. econs. }
      exploit eval_condition_join_binded; eauto.
      i. rewrite H1. inv EVAL. simpl. esplits; eauto. simpl.
      eapply normalize_binded; eauto. destruct b; eauto.
    + destruct (ptr_binop op) eqn:PTRBINOP.
      (* ptr binop *)
      { unfold eval_operation_wrapper in *. rewrite PTROP in EVAL.
        assert (EVAL1: eval_operation_join genv sp op vl m = Some v) by (destruct op; ss).
        clear EVAL. exploit eval_operation_join_binded; eauto. i. des. rewrite EVAL2.
        esplits; eauto. rewrite PTROP. destruct op; simpl in *; clarify. }
      unfold ptr_op, ptr_cond in PTROP. (* rewrite BIT in *. *)
      destruct op; simpl in *; try rewrite BIT in *; inv PTROP; inv PTRBINOP.
      { rewrite H0 in H1. inv H1. }
      unfold ptr_uncond, ptr_bincond in *. rewrite BIT in *. simpl in *.
      (* sel *)
      destruct c; simpl in *; inv H0.
      2:{ unfold eval_operation_wrapper in *.
          (* simpl in *. *) do 2 (destruct BIND;[inv EVAL|]).
          assert (PTRCMP: ptr_op (Osel (Ccompuimm c n) t) = true).
          { simpl. unfold ptr_cond. eapply orb_true_intro. left. simpl. eauto. }
          rewrite PTRCMP in *.
          destruct ((eval_condition_join (Ccompuimm c n) vl1 m)) eqn:COND1.
          2:{ simpl in EVAL. inv EVAL. esplits; eauto. econs. }
          exploit eval_condition_join_binded; eauto.
          i. rewrite H1. inv EVAL. simpl. esplits; eauto. simpl.
          eapply normalize_binded; eauto. destruct b; eauto. }
      unfold eval_operation_wrapper in *.
      (* simpl in *. *) do 2 (destruct BIND;[inv EVAL|]).
      assert (PTRCMP: ptr_op (Osel (Ccompu c) t) = true).
      { simpl. unfold ptr_cond. eapply orb_true_intro. right. simpl. eauto. }
      rewrite PTRCMP in *.
      destruct ((eval_condition_join (Ccompu c) vl1 m)) eqn:COND1.
      2:{ simpl in EVAL. inv EVAL. esplits; eauto. econs. }
      exploit eval_condition_join_binded; eauto.
      i. rewrite H1. inv EVAL. simpl. esplits; eauto. simpl.
      eapply normalize_binded; eauto. destruct b; eauto.
Qed.

End EVAL_WRAPPER_REFINE.
