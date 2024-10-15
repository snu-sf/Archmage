From compcert Require Import Globalenvs Smallstep Simulation AST Integers Events Behaviors Errors Memory Values Maps.
From compcert Require Import Ctypes Clight Clightdefs Globalenvs.
From Paco Require Export paco.
Require Import String CoqlibCCR.

Definition match_temps le le' := forall id, CoqlibCCR.option_rel Val.lessdef (le ! id) (le' ! id).

Inductive match_cont : cont -> cont -> Prop :=
  | match_Kstop : match_cont Kstop Kstop
  | match_Kseq
        s k k'
        (NEXT: match_cont k k') :
      match_cont (Kseq s k) (Kseq s k')
  | match_Kloop1
        s1 s2 k k'
        (NEXT: match_cont k k') :
      match_cont (Kloop1 s1 s2 k) (Kloop1 s1 s2 k')
  | match_Kloop2
        s1 s2 k k'
        (NEXT: match_cont k k') :
      match_cont (Kloop2 s1 s2 k) (Kloop2 s1 s2 k')
  | match_Kswitch
        k k'
        (NEXT: match_cont k k') :
      match_cont (Kswitch k) (Kswitch k')
  | match_Kcall
        id f e le le' k k'
        (LEINJ: match_temps le le')
        (NEXT: match_cont k k') :
      match_cont (Kcall id f e le k) (Kcall id f e le' k').

Variant match_states : state -> state -> Prop :=
  | match_state
        f s k k' e le le' m m'
        (EXT: Mem.extends m m')
        (LEINJ: match_temps le le')
        (NEXT: match_cont k k') :
      match_states (State f s k e le m) (State f s k' e le' m')
  | match_callstate
        fd args args' k k' m m'
        (EXT: Mem.extends m m')
        (VALINJ: Val.lessdef_list args args')
        (NEXT: match_cont k k') :
      match_states (Callstate fd args k m) (Callstate fd args' k' m')
  | match_returnstate
        res res' k k' m m'
        (EXT: Mem.extends m m')
        (VALINJ: Val.lessdef res res')
        (NEXT: match_cont k k') :
      match_states (Returnstate res k m) (Returnstate res' k' m').

Lemma match_call_cont
    k k'
    (MC: match_cont k k')
    (IS: is_call_cont k') :
  is_call_cont k.
Proof. unfold is_call_cont in *. des_ifs; inv MC. Qed.

Lemma match_free_list
    m m' m0 m0' l
    (MM: Mem.extends m m')
    (FREE: Mem.free_list m' l = Some m0')
    (FREE0: Mem.free_list m l = Some m0) :
  Mem.extends m0 m0'.
Proof.
  ginduction l; i; ss; eauto; clarify.
  des_ifs_safe.
  hexploit Mem.free_parallel_extends; eauto.
  i. des. clarify. eapply IHl; eauto.
Qed.

Lemma match_free_list_match
    m m' m0 l
    (MM: Mem.extends m m')
    (FREE: Mem.free_list m l = Some m0) :
  exists m0', Mem.free_list m' l = Some m0' /\ Mem.extends m0 m0'.
Proof.
  ginduction l; i; ss; clarify. { esplits; eauto. }
  des_ifs_safe.
  hexploit Mem.free_parallel_extends; eauto.
  i. des. des_ifs. eapply IHl; eauto.
Qed.

Lemma match_sem_cast_match
    m m' v v' ty1 ty2 v0' v0
    (MM: Mem.extends m m')
    (CAST: Cop.sem_cast v' ty1 ty2 m' = Some v0')
    (CAST': Cop.sem_cast v ty1 ty2 m = Some v0)
    (MV: Val.lessdef v v') :
  Val.lessdef v0 v0'.
Proof.
  unfold Cop.sem_cast in *. des_ifs; inv MV; ss; clarify.
Qed.

Lemma match_sem_cast
    m m' v v' ty1 ty2 v0
    (MM: Mem.extends m m')
    (CAST: Cop.sem_cast v ty1 ty2 m = Some v0)
    (MV: Val.lessdef v v') :
  exists v0', Cop.sem_cast v' ty1 ty2 m' = Some v0'.
Proof.
  unfold Cop.sem_cast in *. des_ifs; inv MV; ss; clarify; eauto.
  hexploit Mem.weak_valid_pointer_extends; eauto. i. clarify.
Qed.

Lemma match_sem_un_match
    m m' o v v' ty v0' v0
    (MM: Mem.extends m m')
    (OP: Cop.sem_unary_operation o v' ty m' = Some v0')
    (OP': Cop.sem_unary_operation o v ty m = Some v0)
    (MV: Val.lessdef v v') :
  Val.lessdef v0 v0'.
Proof.
  destruct o; ss.
  - unfold Cop.sem_notbool in *. unfold Cop.bool_val in *. des_ifs; inv MV; ss; clarify.
  - unfold Cop.sem_notint in *. des_ifs; inv MV; ss; clarify.
  - unfold Cop.sem_neg in *. des_ifs; inv MV; ss; clarify.
  - unfold Cop.sem_absfloat in *. des_ifs; inv MV; ss; clarify.
Qed.

Lemma match_sem_un
    m m' o v v' ty v0
    (MM: Mem.extends m m')
    (OP': Cop.sem_unary_operation o v ty m = Some v0)
    (MV: Val.lessdef v v') :
  exists v0', Cop.sem_unary_operation o v' ty m' = Some v0'.
Proof.
  destruct o; ss.
  - unfold Cop.sem_notbool in *. unfold Cop.bool_val in *. des_ifs; inv MV; ss; clarify; eauto.
    hexploit Mem.weak_valid_pointer_extends; eauto. i. clarify.
  - unfold Cop.sem_notint in *. des_ifs; inv MV; ss; clarify; eauto.
  - unfold Cop.sem_neg in *. des_ifs; inv MV; ss; clarify; eauto.
  - unfold Cop.sem_absfloat in *. des_ifs; inv MV; ss; clarify; eauto.
Qed.

Ltac wd :=
  match goal with
  | H: IntPtrRel.to_ptr_val _ _ = Vlong _ |- _ => unfold IntPtrRel.to_ptr_val, Mem.to_ptr in H; des_ifs
  | H: IntPtrRel.to_int_val _ _ = Vptr _ _ |- _ => unfold IntPtrRel.to_int_val, Mem.to_int in H; des_ifs
  end.

Ltac re :=
  match goal with
  | H: Int.eq _ _ = true |- _ => apply Int.same_if_eq in H
  | H: Int64.eq _ _ = true |- _ => apply Int64.same_if_eq in H
  | H: Ptrofs.eq _ _ = true |- _ => apply Ptrofs.same_if_eq in H
  end.

Lemma match_sem_ptr_sub_match
    m m' v1 v2 i
    (MM: Mem.extends m m')
    (OP: Cop._sem_ptr_sub_join v1 v2 m = Some i) :
  Cop._sem_ptr_sub_join v1 v2 m' = Some i.
Proof.
  unfold Cop._sem_ptr_sub_join in OP. des_ifs.
  - apply Ptrofs.same_if_eq in Heq1. clarify.
    unfold Cop._sem_ptr_sub in Heq, Heq0. des_ifs; repeat wd; try solve [ss; des_ifs].
    + repeat wd. repeat re. clarify. ss. unfold Vnullptr in *. clarify.
      unfold IntPtrRel.to_int_val in *. ss. clarify. unfold Cop._sem_ptr_sub_join.
      unfold IntPtrRel.to_ptr_val. ss.
      des_ifs; unfold Cop._sem_ptr_sub in *; des_ifs.
      { repeat re. rewrite Heq1. ss. rewrite Heq5. eauto. }
      ss. unfold Vnullptr in *. clarify.
    + unfold IntPtrRel.to_ptr_val, IntPtrRel.to_int_val in *.
      unfold IntPtrRel.option_to_val in *. des_ifs.
      hexploit (Mem.to_ptr_extends m v1 v1); eauto. i.
      hexploit (Mem.to_ptr_extends m v2 v2); eauto. i.
      hexploit (Mem.to_int_extends m v1 v1); eauto. i.
      hexploit (Mem.to_int_extends m v2 v2); eauto. i.
      unfold Cop._sem_ptr_sub_join, Cop._sem_ptr_sub, IntPtrRel.to_int_val, IntPtrRel.to_ptr_val.
      rewrite H, H0, H1, H2. ss. des_ifs.
      { repeat re. f_equal. etransitivity; eauto. }
      rewrite Heq5 in Heq7. rewrite Heq in Heq7. unfold Ptrofs.eq in Heq7. ss. des_ifs.
  - clear Heq0. unfold Cop._sem_ptr_sub in Heq. des_ifs; repeat wd; try solve [ss; des_ifs]; ss.
    { repeat re. unfold Vnullptr in *. clarify. }
    unfold IntPtrRel.to_ptr_val in *.
    unfold IntPtrRel.option_to_val in *. des_ifs.
    hexploit (Mem.to_ptr_extends m v1 v1); eauto. i.
    hexploit (Mem.to_ptr_extends m v2 v2); eauto. i.
    unfold Cop._sem_ptr_sub_join, Cop._sem_ptr_sub, IntPtrRel.to_ptr_val.
    rewrite H, H0. ss. des_ifs; try solve [repeat wd; ss; des_ifs].
    hexploit IntPtrRel.psubl_wrapper_no_angelic.
    { unfold IntPtrRel.to_ptr_val. rewrite H. rewrite H0. ss. }
    { rewrite Heq4. rewrite Heq5. ss. }
    i. ss; des; des_ifs; clarify. unfold lib.sflib.NW in *. des; clarify.
    exfalso. hexploit Ptrofs.eq_spec. rewrite Heq3. i. apply H2.
    rewrite <- Ptrofs.of_int64_to_int64 at 1; ss. f_equal. apply Int64.same_if_eq.
    unfold Int64.eq. des_ifs.
  - clear Heq. unfold Cop._sem_ptr_sub in Heq0. des_ifs; repeat wd; try solve [ss; des_ifs]; ss.
    unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *. des_ifs.
    hexploit (Mem.to_int_extends m v1 v1); eauto. i.
    hexploit (Mem.to_int_extends m v2 v2); eauto. i.
    unfold Cop._sem_ptr_sub_join, Cop._sem_ptr_sub, IntPtrRel.to_int_val.
    rewrite H, H0. ss. des_ifs; try solve [re; f_equal; eauto].
    { repeat wd. repeat re. ss. unfold Vnullptr in *. clarify. }
    hexploit IntPtrRel.psubl_wrapper_no_angelic.
    { rewrite Heq4. rewrite Heq5. ss. }
    { unfold IntPtrRel.to_int_val. rewrite H. rewrite H0. ss. }
    i. unfold lib.sflib.NW in *. ss; des; des_ifs; clarify.
    exfalso. hexploit Ptrofs.eq_spec. rewrite Heq3. i. apply H1.
    rewrite <- Ptrofs.of_int64_to_int64 at 1; ss. f_equal. rewrite Heq7.
    apply Int64.same_if_eq. unfold Int64.eq. des_ifs.
Qed.

Lemma match_sem_ptr_match
    m m' o v1 v2 v1' v2' v
    (MM: Mem.extends m m')
    (OP: Cop.cmp_ptr m o v1 v2 = Some v)
    (MV1: Val.lessdef v1 v1')
    (MV2: Val.lessdef v2 v2') :
  exists v', Cop.cmp_ptr m' o v1' v2' = Some v' /\ Val.lessdef v v'.
Proof.
  unfold Cop.cmp_ptr, Coqlib.option_map, IntPtrRel.cmplu_join_common in OP. des_ifs.
  - inv MV1. inv MV2. unfold Cop.cmp_ptr. ss. des_ifs. ss. et.
  - inv MV1. inv MV2. unfold Val.cmplu_bool in Heq. des_ifs. apply andb_prop in Heq3. des.
    hexploit Mem.weak_valid_pointer_extends; et.
    i. unfold Mem.weak_valid_pointer in *.
    unfold Cop.cmp_ptr. ss. des_ifs. rewrite Heq. ss. et.
  - inv MV1. inv MV2.
    eapply IntPtrRel.cmplu_join_lessdef in Heq; et. red in Heq.
    unfold Cop.cmp_ptr. ss. des_ifs. rewrite Heq. ss. et.
  - inv MV1. inv MV2. unfold Val.cmplu_bool in Heq. des_ifs. apply andb_prop in Heq3. des.
    hexploit Mem.weak_valid_pointer_extends; et. i. move Heq2 at bottom.
    hexploit Mem.weak_valid_pointer_extends; et. i.
    unfold Mem.weak_valid_pointer in *.
    unfold Cop.cmp_ptr. ss. des_ifs. ss. rewrite Heq. ss. et.
  - inv MV1. inv MV2. 
    eapply IntPtrRel.cmplu_join_lessdef in Heq; et. red in Heq.
    unfold Cop.cmp_ptr. ss. des_ifs. rewrite Heq. ss. et.
  - inv MV1. inv MV2. unfold Val.cmplu_bool in Heq. des_ifs.
    + apply andb_prop in Heq2. des.
      hexploit Mem.weak_valid_pointer_extends; et. i. move Heq2 at bottom.
      hexploit Mem.weak_valid_pointer_extends; et. i.
      unfold Mem.weak_valid_pointer in *.
      unfold Cop.cmp_ptr. ss. des_ifs. ss. et.
    + apply andb_prop in Heq2. des.
      hexploit Mem.valid_pointer_extends; et. i. move Heq2 at bottom.
      hexploit Mem.valid_pointer_extends; et. i.
      unfold Cop.cmp_ptr. ss. des_ifs. ss. rewrite Heq. ss. et.
Qed.

Lemma match_to_ptr_match
    m m' v
    (MM: Mem.extends m m') :
  Val.lessdef (IntPtrRel.to_ptr_val m v) (IntPtrRel.to_ptr_val m' v).
Proof.
  unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val. des_ifs.
  - hexploit Mem.to_ptr_extends. apply MM. 2: et. et. i. rewrite H in *. clarify.
  - hexploit Mem.to_ptr_extends. apply MM. 2: et. et. i. rewrite H in *. clarify.
Qed.

Lemma match_to_int_match
    m m' v
    (MM: Mem.extends m m') :
  Val.lessdef (IntPtrRel.to_int_val m v) (IntPtrRel.to_int_val m' v).
Proof.
  unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val. des_ifs.
  - hexploit Mem.to_int_extends. apply MM. 2: et. et. i. rewrite H in *. clarify.
  - hexploit Mem.to_int_extends. apply MM. 2: et. et. i. rewrite H in *. clarify.
Qed.

(* Lemma match_sem_ptr_join_match *)
(*     m m' o v1 v2 v *)
(*     (MM: Mem.extends m m') *)
(*     (OP: Cop.cmp_ptr_join m o v1 v2 = Some v) : *)
(*   exists v', Cop.cmp_ptr_join m' o v1 v2 = Some v' /\ Val.lessdef v v'. *)
(* Proof. *)
(*   unfold Cop.cmp_ptr_join in OP. des_ifs. *)
(*   - re. clarify. *)
(*     hexploit match_sem_ptr_match. et. apply Heq. apply match_to_ptr_match; et. *)
(*     apply match_to_ptr_match; et. i. des. *)
(*     hexploit match_sem_ptr_match. et. apply Heq0. apply match_to_int_match; et. *)
(*     apply match_to_int_match; et. i. des. inv H0. inv H2. *)
(*     unfold Cop.cmp_ptr_join. des_ifs; et. unfold Int.eq in *. des_ifs. *)
(*   - hexploit match_sem_ptr_match. et. apply Heq. apply match_to_ptr_match; et. *)
(*     apply match_to_ptr_match; et. i. des. inv H0. *)
(*     unfold Cop.cmp_ptr_join. des_ifs; et; exfalso. *)
(*     all: try solve [clear -Heq2; unfold Cop.cmp_ptr, Coqlib.option_map in Heq2; des_ifs; try solve [destruct b; ss; clarify| destruct b0; ss; clarify]]. *)
(*     clear Heq Heq0. unfold Cop.cmp_ptr, Coqlib.option_map in *. des_ifs. *)
(*     hexploit IntPtrRel.cmplu_no_angelic; et. i. rewrite H in *. rewrite H0 in *. *)
(*     clarify. unfold Int.eq in *. des_ifs. *)
(*   - hexploit match_sem_ptr_match. et. apply Heq0. apply match_to_int_match; et. *)
(*     apply match_to_int_match; et. i. des. inv H0. *)
(*     unfold Cop.cmp_ptr_join. des_ifs; et. 2:{ re. clarify. et. } all: exfalso. *)
(*     all: try solve [clear -Heq1; unfold Cop.cmp_ptr, Coqlib.option_map in Heq1; des_ifs; try solve [destruct b; ss; clarify| destruct b0; ss; clarify]]. *)
(*     clear Heq Heq0. unfold Cop.cmp_ptr, Coqlib.option_map in *. des_ifs. *)
(*     hexploit IntPtrRel.cmplu_no_angelic; et. i. rewrite H in *. rewrite H0 in *. *)
(*     clarify. unfold Int.eq in *. des_ifs. *)
(* Qed. *)

(* Lemma match_sem_ptr_cmp_common_match *)
(*     m m' o v1 v2 v *)
(*     (MM: Mem.extends m m') *)
(*     (OP: Cop.cmp_ptr_join_common m o v1 v2 = Some v) : *)
(*   exists v', Cop.cmp_ptr_join_common m' o v1 v2 = Some v' /\ Val.lessdef v v'. *)
(* Proof. *)
(*   unfold Cop.cmp_ptr_join_common in OP. des_ifs. *)
(*   - unfold Cop.cmp_ptr in *. des_ifs. ss. clarify. ss. *)
(*     unfold Cop.cmp_ptr in *. ss. clarify. ss. esplits; eauto. *)
(*   - unfold Cop.cmp_ptr in *. des_ifs. ss. clarify. ss. *)
(*     unfold Cop.cmp_ptr in *. ss. clarify. ss. esplits; eauto. des_ifs. *)
(*     hexploit Mem.weak_valid_pointer_extends; eauto. i. unfold Mem.weak_valid_pointer in *. *)
(*     clarify. *)
(*   - hexploit match_sem_ptr_join_match; et. i. des. ss. des_ifs. rewrite H. et. *)
(*   - hexploit match_sem_ptr_join_match; et. i. des. ss. des_ifs. rewrite H. et. *)
(*   - ss. des_ifs. hexploit match_sem_ptr_match; et. *)
(*   - ss. des_ifs. hexploit match_sem_ptr_join_match; et. *)
(*   - ss. des_ifs. hexploit match_sem_ptr_match; et. *)
(* Qed. *)

(* TODO: integrate two kinds of lemma to forward sim-lemma *)

Lemma match_sem_bin_match
    ce m m' o v v' ty1 ty2 v0' v0 v1
    (MM: Mem.extends m m')
    (OP': Cop.sem_binary_operation ce o v ty1 v0 ty2 m = Some v1)
    (MV: Val.lessdef v v')
    (MV': Val.lessdef v0 v0') :
  exists v1', Cop.sem_binary_operation ce o v' ty1 v0' ty2 m' = Some v1' /\ Val.lessdef v1 v1'.
Proof.
  destruct o; ss.
  - unfold Cop.sem_add in *. des_ifs; inv MV; inv MV'; ss; clarify; try rewrite OP'; eauto.
    + unfold Cop.sem_add_ptr_int in *. des_ifs.
    + unfold Cop.sem_add_ptr_long in *. des_ifs.
    + unfold Cop.sem_add_ptr_int in *. des_ifs.
    + unfold Cop.sem_add_ptr_long in *. des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq2 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H1|inv H2].
      all: inv H1; inv H2; esplits; eauto.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: unfold Cop.sem_cast in Heq1; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: unfold Cop.sem_cast in Heq1; des_ifs.
  - unfold Cop.sem_sub in *. des_ifs; inv MV; inv MV'; ss; clarify; try solve [esplits; eauto].
    + unfold Cop._sem_ptr_sub_join_common in *. des_ifs; try solve [esplits; eauto].
      all: hexploit match_sem_ptr_sub_match; eauto; i; clarify; esplits; eauto.
    + unfold Cop._sem_ptr_sub_join_common in *. des_ifs; try solve [esplits; eauto].
      all: hexploit match_sem_ptr_sub_match; eauto; i; clarify; esplits; eauto.
    + unfold Cop._sem_ptr_sub_join_common in *. des_ifs; try solve [esplits; eauto].
      all: hexploit match_sem_ptr_sub_match; eauto; i; clarify; esplits; eauto.
    + unfold Cop._sem_ptr_sub_join_common in *. des_ifs; try solve [esplits; eauto].
      all: hexploit match_sem_ptr_sub_match; eauto; i; clarify; esplits; eauto.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq2 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H|inv H0].
      all: inv H; inv H0; esplits; eauto.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq1; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_mul in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq1 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H1|inv H2].
      all: inv H1; inv H2; esplits; eauto.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_div in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq1 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H1|inv H2].
      all: inv H1; inv H2; esplits; eauto; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_mod in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq1 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H1|inv H2].
      all: inv H1; inv H2; esplits; eauto; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_and in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq1 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H1|inv H2].
      all: inv H1; inv H2; esplits; eauto; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_or in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq1 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H1|inv H2].
      all: inv H1; inv H2; esplits; eauto; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_xor in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: unfold Cop.sem_binarith; des_ifs; ss; try rewrite H in *; try rewrite H0 in *; clarify.
      all: try rewrite Heq1 in *; ss; clarify.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: try solve [inv H1|inv H2].
      all: inv H1; inv H2; esplits; eauto; clarify.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq; des_ifs.
    + unfold Cop.sem_binarith in OP'. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_shl in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
  - unfold Cop.sem_shr in *. des_ifs; inv MV; inv MV'; ss; clarify.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
    + unfold Cop.sem_shift in OP'. des_ifs; ss.
      all: unfold Cop.sem_shift; des_ifs; esplits; eauto.
  - unfold Cop.sem_cmp in *. des_ifs; inv MV; inv MV'; ss; clarify;
    try solve [eapply match_sem_ptr_match; et].
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: inv H1; inv H2.
      all: unfold Cop.sem_binarith; rewrite Heq2; ss; des_ifs; et.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq1; des_ifs.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_cmp in *. des_ifs; inv MV; inv MV'; ss; clarify;
    try solve [eapply match_sem_ptr_match; et].
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: inv H1; inv H2.
      all: unfold Cop.sem_binarith; rewrite Heq2; ss; des_ifs; et.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq1; des_ifs.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_cmp in *. des_ifs; inv MV; inv MV'; ss; clarify;
    try solve [eapply match_sem_ptr_match; et].
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: inv H1; inv H2.
      all: unfold Cop.sem_binarith; rewrite Heq2; ss; des_ifs; et.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq1; des_ifs.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_cmp in *. des_ifs; inv MV; inv MV'; ss; clarify;
    try solve [eapply match_sem_ptr_match; et].
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: inv H1; inv H2.
      all: unfold Cop.sem_binarith; rewrite Heq2; ss; des_ifs; et.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq1; des_ifs.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_cmp in *. des_ifs; inv MV; inv MV'; ss; clarify;
    try solve [eapply match_sem_ptr_match; et].
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: inv H1; inv H2.
      all: unfold Cop.sem_binarith; rewrite Heq2; ss; des_ifs; et.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq1; des_ifs.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
  - unfold Cop.sem_cmp in *. des_ifs; inv MV; inv MV'; ss; clarify;
    try solve [eapply match_sem_ptr_match; et].
    + unfold Cop.sem_binarith in OP'. des_ifs; ss.
      all: hexploit (match_sem_cast m m' v' v'); eauto; i; des.
      all: hexploit (match_sem_cast m m' v0' v0'); eauto; i; des.
      all: hexploit (match_sem_cast_match m m' v' v'); eauto; i.
      all: hexploit (match_sem_cast_match m m' v0' v0'); eauto; i.
      all: inv H1; inv H2.
      all: unfold Cop.sem_binarith; rewrite Heq2; ss; des_ifs; et.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq1; des_ifs.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
    + exfalso.
      unfold Cop.sem_binarith in *. des_ifs.
      all: unfold Cop.sem_cast in Heq0; des_ifs.
Qed.


Lemma match_deref_loc_match
    t m m' vp vp' v v'
    (MM: Mem.extends m m')
    (DEREF: deref_loc t m vp v)
    (DEREF': deref_loc t m' vp' v')
    (MV: Val.lessdef vp vp') :
  Val.lessdef v v'.
Proof.
  inv DEREF; inv DEREF'; ss; clarify; rewrite H in *; clarify.
  hexploit Mem.loadv_extends; eauto. i. des. clarify.
Qed.

Lemma match_deref_loc
    t m m' vp vp' v
    (MM: Mem.extends m m')
    (DEREF: deref_loc t m vp v)
    (MV: Val.lessdef vp vp') :
  exists v', deref_loc t m' vp' v' /\ Val.lessdef v v'.
Proof.
  inv DEREF.
  - hexploit Mem.loadv_extends; et. i. des. esplits; et. econs; et.
  - esplits; et. econs 2. et.
  - esplits; et. econs 3. et.
Qed.

Lemma match_eval_match
    ge e le le' m m' a
    (MM: Mem.extends m m')
    (MLE: match_temps le le') :
  (forall v, Clight.eval_expr ge e le m a v -> exists v', Clight.eval_expr ge e le' m' a v' /\ Val.lessdef v v')
  /\ (forall v, Clight.eval_lvalue ge e le m a v -> exists v', Clight.eval_lvalue ge e le' m' a v' /\ Val.lessdef v v').
Proof.
  ginduction a; i; ss; clarify.
  (* case: constant *)
  - split; i; inv H; try solve [inv H0]. esplits; et. econs.
  - split; i; inv H; try solve [inv H0]. esplits; et. econs.
  - split; i; inv H; try solve [inv H0]. esplits; et. econs.
  - split; i; inv H; try solve [inv H0]. esplits; et. econs.
  (* case: Evar *)
  - split; i; inv H.
    + hexploit match_deref_loc; et. i. des. esplits; et. econs; et. inv H0.
      { econs; et. } econs 2; et.
    + esplits; et. econs. et.
    + esplits; et. econs 2; et.
  (* case: Etempvar *)
  - split; i; inv H; try solve [inv H0].
    specialize (MLE i). rewrite H3 in *. inv MLE. esplits; et. econs; et.
  (* case: Ederef *)
  - hexploit IHa; eauto. i. des. split; i; inv H1.
    + inv H2. hexploit H; et. i. des. hexploit match_deref_loc; et. i. des. esplits; et.
      econs; et. econs; et. destruct lv; clarify; inv H2; ss.
    + hexploit H; et. i. des. esplits; et. econs; et.
      destruct v; clarify; inv H2; ss.
  (* case: Eaddrof *)
  - hexploit IHa; eauto. i. des. split; i; inv H1; try solve [inv H2].
    hexploit H0; et. i. des. esplits; et. econs. et.
  (* case: Eunop *)
  - hexploit IHa; eauto. i. des. split; i; inv H1; try solve [inv H2].
    hexploit H; eauto. i. des. hexploit match_sem_un; eauto. i. des.
    hexploit match_sem_un_match; et. i. esplits; et. econs; et.
  (* case: Ebinop *)
  - hexploit IHa1; eauto. i. des. hexploit IHa2; eauto. i. des.
    split; i; inv H3; try solve [inv H4].
    hexploit H; eauto. hexploit H1; eauto. i. des. hexploit match_sem_bin_match; eauto.
    i. des. esplits; et. econs; et.
  (* case: Ecast *)
  - hexploit IHa; et. i. des. split; i; inv H1; try solve [inv H2].
    hexploit H; et. i. des. hexploit match_sem_cast; et. i. des.
    hexploit match_sem_cast_match; et. i. esplits; et. econs; et.
  (* case: Efield *)
  - hexploit IHa; et. i. des. split; i; inv H1.
    + inv H2.
      * hexploit H; et. i. des. hexploit match_deref_loc. et. et.
        { instantiate (1:=if Archi.ptr64 then Val.addl v' (Vptrofs (Ptrofs.repr delta)) else Val.add v' (Vptrofs (Ptrofs.repr delta))).
          inv H2; ss. }
        i. des. esplits; et.
        econs; et. econs; et. inv H2; ss.
      * hexploit H; et. i. des. hexploit match_deref_loc; et. i. des. esplits; et.
        econs; et. eapply eval_Efield_union; et. inv H2; ss.
    + hexploit H; et. i. des.
      exists (if Archi.ptr64 then Val.addl v' (Vptrofs (Ptrofs.repr delta)) else Val.add v' (Vptrofs (Ptrofs.repr delta))).
      esplits. { econs; et. inv H2; ss. } { inv H2; ss. }
    + hexploit H; et. i. des. esplits; et.
      eapply eval_Efield_union; et. inv H2; ss.
  (* case: Esizeof *)
  - split; i; inv H; try solve [inv H0]. esplits; et. econs.
  (* case: Ealignof *)
  - split; i; inv H; try solve [inv H0]. esplits; et. econs.
Qed.

Lemma match_eval_expr_match
    ge e le le' m m' a v
    (MM: Mem.extends m m')
    (MLE: match_temps le le')
    (OP: Clight.eval_expr ge e le m a v) :
  exists v', Clight.eval_expr ge e le' m' a v' /\ Val.lessdef v v'.
Proof.
  hexploit match_eval_match; eauto. i. des. et.
Qed.

Lemma match_eval_exprlist_match
    ge e le le' m m' al tl vl
    (MM: Mem.extends m m')
    (MLE: match_temps le le')
    (OP: Clight.eval_exprlist ge e le m al tl vl) :
  exists vl', Clight.eval_exprlist ge e le' m' al tl vl' /\ Val.lessdef_list vl vl'.
Proof.
  ginduction OP; i; ss.
  - esplits; et. econs.
  - hexploit match_eval_expr_match; eauto. i. des.
    hexploit match_sem_cast; eauto. i. des.
    hexploit match_sem_cast_match; eauto. i.
    hexploit IHOP; et. i. des.
    esplits; et. econs; et.
Qed.

Lemma match_eval_lvalue_match
    ge e le le' m m' a v
    (MM: Mem.extends m m')
    (MLE: match_temps le le')
    (OP: Clight.eval_lvalue ge e le m a v) :
  exists v', Clight.eval_lvalue ge e le' m' a v' /\ Val.lessdef v v'.
Proof.
  hexploit match_eval_match; eauto. i. des. et.
Qed.

Lemma match_assign_loc_match
    ce m m0 m' m0' vp vp' v v' ty
    (MM: Mem.extends m m')
    (ASN: assign_loc ce ty m vp v m0)
    (ASN': assign_loc ce ty m' vp' v' m0')
    (MV: Val.lessdef vp vp')
    (MV': Val.lessdef v v') :
  Mem.extends m0 m0'.
Proof.
  inv ASN; inv ASN'; clarify; rewrite H in *; clarify; try solve [nia].
  - hexploit Mem.storev_extends; et. i. des. rewrite H1 in *. clarify.
  - hexploit Mem.to_ptr_extends; et. i. rewrite H11 in *. clarify.
    hexploit Mem.to_ptr_extends. 3: apply TOPTR1. all: et. i. rewrite H12 in *. clarify.
    hexploit Mem.loadbytes_extends; et. i. destruct H13 as [bytes2 [H13 H14]].
    rewrite H13 in H9. clarify.
    hexploit Mem.storebytes_within_extends; et. i. destruct H9 as [m2' [H15 H16]].
    rewrite H15 in *. clarify.
Qed.

Lemma match_assign_loc
    ce m m' m0 vp vp' v v' ty
    (MM: Mem.extends m m')
    (ASN: assign_loc ce ty m vp v m0)
    (MV: Val.lessdef vp vp')
    (MV': Val.lessdef v v') :
  exists m0', assign_loc ce ty m' vp' v' m0'.
Proof.
  inv ASN.
  - hexploit Mem.storev_extends; et. i. des. eexists. econs; et.
  - hexploit Mem.to_ptr_extends; et. i.
    hexploit Mem.to_ptr_extends. 3: apply TOPTR1. all: et. i.
    hexploit Mem.loadbytes_extends; et. i. destruct H7 as [bytes2 [H7 H8]].
    hexploit Mem.storebytes_within_extends; et. i. destruct H9 as [m2' [H10 H11]].
    econs. econs 2; et.
  - econs. econs 3; et.
Qed.

Scheme stmt_ind := Induction for statement Sort Prop
  with lstmt_ind := Induction for labeled_statements Sort Prop.

Lemma find_label_aux0
    k k0 l s
    (MK: match_cont k k0):
  find_label l s k = None -> find_label l s k0 = None.
Proof.
  revert k k0 l MK.
  set (p := fun s => forall k k0 l, match_cont k k0 -> find_label l s k = None -> find_label l s k0 = None).
  set (p0 := fun ls => forall k k0 lbl, match_cont k k0 -> find_label_ls lbl ls k = None -> find_label_ls lbl ls k0 = None).
  hexploit (stmt_ind p p0); et; unfold p, p0 in *; clear p p0.
  all: try solve [i; ss].
  - i. ss. destruct find_label eqn:X; ss. erewrite H; et. econs. et.
  - i. ss. destruct find_label eqn:X; ss. erewrite H; et.
  - i. ss. destruct find_label eqn:X; ss. erewrite H; et. 2:{ econs. et. }
    eapply H0; et. econs. et.
  - i. ss. eapply H; et. econs. et.
  - i. ss. des_ifs. et.
  - i. ss. destruct find_label eqn:X; ss. erewrite H; et. econs. et.
Qed.

Lemma find_label_aux1
    k k0 lbl sl
    (MK: match_cont k k0):
  find_label_ls lbl sl k = None -> find_label_ls lbl sl k0 = None.
Proof.
  ginduction sl; i; ss.
  destruct find_label eqn:X; ss. eapply find_label_aux0 in X.
  2:{ econs. et. } rewrite X. et.
Qed.

Lemma find_label_aux2
    k k0 l s s' k'
    (MK: match_cont k k0)
    (L: find_label l s k = Some (s', k')) :
  exists k0', find_label l s k0 = Some (s', k0') /\ match_cont k' k0'.
Proof.
  revert s' k k0 k' l L MK.
  set (p := fun s => forall s' k k0 k' l, match_cont k k0 -> find_label l s k = Some (s', k') -> exists k0', find_label l s k0 = Some (s', k0') /\ match_cont k' k0').
  set (p0 := fun ls => forall s' k k0 k' lbl, match_cont k k0 -> find_label_ls lbl ls k = Some (s', k') -> exists k0', find_label_ls lbl ls k0 = Some (s', k0') /\ match_cont k' k0').
  hexploit (stmt_ind p p0); et; unfold p, p0 in *; clear p p0.
  all: try solve [i; ss].
  - i. ss. destruct find_label eqn:X; ss; clarify.
    + hexploit H. 2: et. econs. et. i. des. des_ifs. et.
    + eapply find_label_aux0 in X. 2:{ econs. et. } des_ifs. et.
  - i. ss. destruct find_label eqn:X; ss; clarify.
    + hexploit H; et. i. des. des_ifs. et.
    + eapply find_label_aux0 in X; et. des_ifs. et.
  - i. ss. destruct find_label eqn:X; ss; clarify.
    + hexploit H. 2: et. econs. et. i. des. des_ifs. et.
    + eapply find_label_aux0 in X. 2: econs; et. rewrite X.
      eapply H0. 2: et. econs; et.
  - i. ss. eapply H. 2: et. econs. et.
  - i. ss. des_ifs; et.
  - i. ss. destruct find_label eqn:X; ss; clarify.
    + hexploit H. 2: et. econs; et. i. des. des_ifs. et.
    + eapply find_label_aux0 in X. 2: econs; et. des_ifs. et.
Qed.

Lemma find_label_aux3
    k k0 lbl sl s' k'
    (MK: match_cont k k0)
    (L: find_label_ls lbl sl k = Some (s', k')) :
  exists k0', find_label_ls lbl sl k0 = Some (s', k0') /\ match_cont k' k0'.
Proof.
  ginduction sl; ss.
  i. destruct find_label eqn:X; ss; clarify.
  - eapply find_label_aux2 in X. 2: econs; et. des. des_ifs. et.
  - eapply find_label_aux0 in X. 2: econs; et. des_ifs. et.
Qed.

Lemma match_alloc_variables_match
    ge e e' m m0 l m'
    (OP: alloc_variables ge e m l e' m')
    (MM: Mem.extends m m0):
  exists m0', alloc_variables ge e m0 l e' m0' /\ Mem.extends m' m0'.
Proof.
  ginduction OP; i; ss.
  - esplits; et. econs.
  - hexploit Mem.alloc_extends; et. instantiate (1:=0%Z). ss. instantiate (1:=sizeof ge ty). nia.
    i. des. hexploit IHOP; et. i. des. esplits; et. econs; et.
Qed.

Require Import ClightPlusLenvSim.

Lemma match_bind_parameter_temps
    params sle rvs rvs' sbase tbase
    (BIND_SRC: bind_parameter_temps params rvs sbase = Some sle)
    (MLE: match_temps sbase tbase)
    (MV: Val.lessdef_list rvs rvs') :
  exists tle, (<<BIND_TGT: Clight.bind_parameter_temps params rvs' tbase = Some tle>>).
Proof.
  apply (bind_parameter_temps_exists_if_same_length' params rvs' tbase).
  clear -BIND_SRC MV. depgen sbase.
  revert sle. depgen rvs. depgen params.
  induction rvs'; i; ss; des_ifs. { inv MV. destruct params; ss. des_ifs. }
  inv MV. destruct params; ss. des_ifs. f_equal. et.
Qed.

Lemma match_bind_parameter_temps_match
    params sle tle rvs rvs' sbase tbase
    (BIND_SRC: bind_parameter_temps params rvs sbase = Some sle)
    (BIND_TGT: Clight.bind_parameter_temps params rvs' tbase = Some tle)
    (MLE: match_temps sbase tbase)
    (MV: Val.lessdef_list rvs rvs') :
  match_temps sle tle.
Proof.
  depgen sbase. depgen sle. depgen rvs. depgen params. revert tle tbase.
  induction rvs'; i; ss; des_ifs. { inv MV. destruct params; ss; clarify. des_ifs. }
  inv MV. destruct params; ss. des_ifs.
  eapply IHrvs'; et. ii. destruct (Pos.eq_dec i id); clarify. { rewrite ! PTree.gss; et. }
  rewrite ! PTree.gso; et.
Qed.

Lemma match_temps_refl le: match_temps le le.
Proof. ii. destruct (le ! id); et. Qed.

Lemma match_function_entry2_match
    ge f args args' m m' e le m1
    (OP: function_entry2 ge f args m e le m1)
    (MV: Val.lessdef_list args args')
    (MM: Mem.extends m m') :
  exists m1' le', function_entry2 ge f args' m' e le' m1' /\ match_temps le le' /\ Mem.extends m1 m1'.
Proof.
  inv OP. hexploit match_bind_parameter_temps; et. apply match_temps_refl.
  i. des. hexploit match_bind_parameter_temps_match. 4: et. all: et.
  apply match_temps_refl. i. hexploit match_alloc_variables_match; et. i. des.
  esplits; et. econs; et.
Qed.

Require Import ClightPlusExprgen ClightPlusSimAll.

Lemma match_states_bsim p gmtgt st_src st_tgt
  (M: match_states st_src st_tgt)
:
  NOSTUTTER.bsim (semantics3 p) (semantics2 p) gmtgt lt 0%nat st_src st_tgt.
Proof.
  revert_until st_src. revert st_src. pcofix CIH.
  i. inv M.
  - destruct s.
    + pfold. econs. i. rr.
      unfold safe in *. hexploit SAFESRC. { apply star_refl. }
      i. des. { inv H. } econs.
      * i. left. inv STEPTGT.
        ** inv NEXT. esplits.
            { instantiate (1:=E0). econs. }
            { left. apply plus_one. econs. }
            { right. apply CIH. econs; eauto. }
        ** inv NEXT. esplits.
            { instantiate (1:=E0). econs. }
            { left. apply plus_one. econs. eauto. }
            { right. apply CIH. econs; eauto. econs; eauto. }
        ** inv NEXT. esplits.
            { instantiate (1:=E0). econs. }
            { left. apply plus_one. econs. }
            { right. apply CIH. econs; eauto. }
        ** hexploit match_call_cont; eauto. i.
           inv H; ss. hexploit match_free_list; eauto. i.
           esplits.
           { instantiate (1:=E0). econs. }
           { left. apply plus_one. econs; eauto. }
           { right. apply CIH. econs; eauto. }
        ** inv NEXT. esplits.
            { instantiate (1:=E0). econs. }
            { left. apply plus_one. apply step_skip_break_switch. eauto. }
            { right. apply CIH. econs; eauto. }
      * i. inv FINALTGT.
      * right. destruct k'.
        ** inv NEXT. inv H. hexploit match_free_list_match; eauto.
           i. des. econs. esplits. apply step_skip_call; eauto.
        ** esplits. econs. econs. econs.
        ** esplits. econs. econs. econs. eauto.
        ** esplits. econs. econs. econs.
        ** econs. esplits. apply step_skip_break_switch. eauto.
        ** inv NEXT. inv H. hexploit match_free_list_match; eauto.
           i. des. econs. esplits. apply step_skip_call; eauto.
    + pfold. econs. i. rr.
      unfold safe in *. hexploit SAFESRC. { apply star_refl. }
      i. des. { inv H. } inv H; des; clarify. econs.
      * i. left. inv STEPTGT; des; clarify.
        hexploit match_eval_expr_match; eauto. i. des.
        hexploit (Clight_eval_expr_determ _ _ _ _ _ _ _ H13 H). i. clarify.
        hexploit match_eval_lvalue_match; eauto. i. des.
        hexploit (Clight_eval_lvalue_determ _ _ _ _ _ _ _ H1 H8). i. clarify.
        hexploit match_sem_cast_match; eauto. i.
        hexploit match_assign_loc_match; eauto. i.
        esplits.
        { econs. }
        { left. apply plus_one. econs; eauto. }
        { right. apply CIH. econs; eauto. }
      * i. inv FINALTGT.
      * right. econs.
        hexploit match_eval_lvalue_match; et. i. des.
        hexploit match_eval_expr_match; et. i. des.
        hexploit match_sem_cast; et. i. des.
        hexploit match_sem_cast_match; et. i.
        hexploit match_assign_loc; et. i. des.
        econs. econs; et.
    + pfold. econs. i. rr.
      unfold safe in *. hexploit SAFESRC. { apply star_refl. }
      i. des. { inv H. } inv H; des; clarify. econs.
      * i. left. inv STEPTGT; des; clarify.
        hexploit match_eval_expr_match; eauto. i. des.
        hexploit (Clight_eval_expr_determ _ _ _ _ _ _ _ H8 H). i. clarify.
        esplits.
        { econs. }
        { left. apply plus_one. econs; eauto. }
        { right. apply CIH. econs; eauto. ii. ss.
          destruct (Pos.eq_dec i id); clarify. { rewrite !PTree.gss. et. }
          rewrite !PTree.gso; et. }
      * i. inv FINALTGT.
      * right. econs.
        hexploit match_eval_expr_match; eauto. i. des.
        econs. econs. et.
    + pfold. econs. i. rr.
      unfold safe in *. hexploit SAFESRC. { apply star_refl. }
      i. des. { inv H. } inv H; des; clarify. econs.
      * i. left. inv STEPTGT; des; clarify. rewrite H9 in *. clarify.
        hexploit match_eval_expr_match; eauto. i. des.
        hexploit (Clight_eval_expr_determ _ _ _ _ _ _ _ H15 H). i. clarify.
        inv H0; ss. rewrite H13 in *. clarify.
        hexploit match_eval_exprlist_match; eauto. i. des.
        hexploit (Clight_eval_exprlist_determ _ _ _ _ _ _ _ _ H16 H0). i. clarify.
        esplits.
        { econs. }
        { left. apply plus_one. econs; eauto. }
        { right. apply CIH. econs; eauto. econs; et. }
      * i. inv FINALTGT.
      * right. econs.
        hexploit match_eval_expr_match; eauto. i. des.
        hexploit match_eval_exprlist_match; eauto. i. des.
        econs. econs; et. inv H0; ss.
    + pfold. econs. i. rr.
      unfold safe in *. hexploit SAFESRC. { apply star_refl. }
      i. des. { inv H. } inv H; des; clarify. econs.
      * i. inv STEPTGT; des; clarify.
        hexploit match_eval_exprlist_match; eauto. i. des.
        hexploit (Clight_eval_exprlist_determ _ _ _ _ _ _ _ _ H10 H). i. clarify.
        destruct (is_external_efb e0) eqn:B.
        { hexploit is_external_ef_reflect. rewrite B. i. inv H1.
          hexploit external_call_mem_extends_backward. 3: et. all: et.
          i. des.
          - left. esplits.
            { instantiate (1:=tr'). clear. apply tr_rel_refl. i. rr.
              des_ifs; esplits; et; rr; des_ifs.
              all: induction l; ss; econs; et; unfold evval_rel, eventval_bind; des_ifs. }
            { left. apply plus_one. econs; et. }
            { right. apply CIH. econs; eauto. destruct o; ss. ii.
              destruct (Pos.eq_dec i id); clarify. { rewrite !PTree.gss. et. }
              rewrite !PTree.gso; et. }
          - exfalso. eapply H1. et.
          - right. unfold lib.sflib.NW in *. des.
            esplits; et. { apply star_one. econs; et. }
            rewrite <- H4. apply tr_rel_refl. i. rr.
            des_ifs; esplits; et; rr; des_ifs.
            all: induction l0; ss; econs; et; unfold evval_rel, eventval_bind; des_ifs. }
        { hexploit is_external_ef_reflect. rewrite B. i. inv H1.
          hexploit external_call_mem_extends. 3: et. all: et. i. des.
          hexploit external_call_determ. et. apply H13. et. i. des. clarify.
          left. esplits.
          { instantiate (1:=t0). clear. apply tr_rel_refl. i. rr.
            des_ifs; esplits; et; rr; des_ifs.
            all: induction l; ss; econs; et; unfold evval_rel, eventval_bind; des_ifs. }
          { left. apply plus_one. econs; et. }
          { right. apply CIH. econs; eauto. destruct o; ss. ii.
              destruct (Pos.eq_dec i id); clarify. { rewrite !PTree.gss. et. }
              rewrite !PTree.gso; et. } }
      * i. inv FINALTGT.
      * right. rr.
        hexploit match_eval_exprlist_match; eauto. i. des.
        destruct (is_external_efb e0) eqn:B.
        { hexploit is_external_ef_reflect. rewrite B. i. inv H1.
          hexploit external_call_mem_extends_backward_progress; eauto.
          i. des. eexists _,_. econs; et. }
        { hexploit is_external_ef_reflect. rewrite B. i. inv H1.
          hexploit external_call_mem_extends. 3: et. all: et. i. des.
          eexists _,_. econs; et. }
    + pfold. econs. i. rr. econs.
      * i. left. inv STEPTGT; des; clarify. esplits.
        { econs. }
        { left. apply plus_one. econs. }
        { right. apply CIH. econs; et. econs. et. }
      * i. inv FINALTGT.
      * right. repeat econs.
    + pfold. econs. i. rr.
      unfold safe in *. hexploit SAFESRC. { apply star_refl. }
      i. des. { inv H. } inv H; des; clarify. econs.
      * i. left. inv STEPTGT; des; clarify.
        hexploit match_eval_expr_match; eauto. i. des.
        hexploit (Clight_eval_expr_determ _ _ _ _ _ _ _ H9 H). i. clarify.
        assert (b = b0); clarify. { clear - H0 H11 H12. unfold Cop.bool_val in *. des_ifs; inv H0; ss. }
        esplits.
        { econs. }
        { left. apply plus_one. econs; eauto. }
        { right. apply CIH. des_ifs; econs; eauto. }
      * i. inv FINALTGT.
      * right.
        hexploit match_eval_expr_match; eauto. i. des.
        econs. econs. econs; et. instantiate (1:=b).
        clear - EXT H0 H11. unfold Cop.bool_val in *. des_ifs; inv H0; ss.
        hexploit Mem.weak_valid_pointer_extends; et.  i. clarify.
    + pfold. econs. i. rr. econs.
      * i. left. inv STEPTGT; des; clarify. esplits.
        { econs. }
        { left. apply plus_one. econs. }
        { right. apply CIH. econs; et. econs. et. }
      * i. inv FINALTGT.
      * right. repeat econs.
    + pfold. econs. i. rr. econs.
      * i. left. inv STEPTGT; des; clarify.
        { inv NEXT. esplits.
          { econs. }
          { left. apply plus_one. econs. }
          { right. apply CIH. econs; et. } }
        { inv NEXT. esplits.
          { econs. }
          { left. apply plus_one. apply step_break_loop1. }
          { right. apply CIH. econs; et. } }
        { inv NEXT. esplits.
          { econs. }
          { left. apply plus_one. apply step_break_loop2. }
          { right. apply CIH. econs; et. } }
        { inv NEXT. esplits.
          { econs. }
          { left. apply plus_one. apply step_skip_break_switch. et. }
          { right. apply CIH. econs; et. } }
      * i. inv FINALTGT.
      * right.
        unfold safe in *. hexploit SAFESRC. { apply star_refl. }
        i. des. { inv H. } inv H; des; clarify.
        { inv NEXT. econs. econs. econs. }
        { inv NEXT. econs. econs. apply step_break_loop1. }
        { inv NEXT. econs. econs. apply step_break_loop2. }
        { inv NEXT. econs. econs. apply step_skip_break_switch. et. }
    + pfold. econs. i. rr. econs.
      * i. left. inv STEPTGT; des; clarify.
        { inv NEXT. esplits.
          { econs. }
          { left. apply plus_one. econs. }
          { right. apply CIH. econs; et. } }
        { inv NEXT. esplits.
          { econs. }
          { left. apply plus_one. apply step_skip_or_continue_loop1. et. }
          { right. apply CIH. econs; et. econs. et. } }
        { inv NEXT. esplits.
          { econs. }
          { left. apply plus_one. apply step_continue_switch. }
          { right. apply CIH. econs; et. } }
      * i. inv FINALTGT.
      * right.
        unfold safe in *. hexploit SAFESRC. { apply star_refl. }
        i. des. { inv H. } inv H; des; clarify.
        { inv NEXT. econs. econs. econs. }
        { inv NEXT. econs. econs. apply step_skip_or_continue_loop1. et. }
        { inv NEXT. econs. econs. apply step_continue_switch. }
    + pfold. econs. i. rr.
      unfold safe in *. hexploit SAFESRC. { apply star_refl. }
      i. des. { inv H. } inv H; des; clarify.
      * econs.
        { i. inv STEPTGT; des; clarify.
          hexploit match_free_list; et. i.
          left. esplits. econs. left. apply plus_one. econs; et.
          right. apply CIH. econs; et.
          clear - NEXT. ginduction k; i; inv NEXT; ss; et. econs.
          econs; et. }
        { i. inv FINALTGT. }
        { right. hexploit match_free_list_match; et. i. des.
          econs. econs. econs; et. }
      * econs.
        { i. inv STEPTGT; des; clarify.
          hexploit match_eval_expr_match; et. i. des.
          hexploit (Clight_eval_expr_determ _ _ _ _ _ _ _ H7 H). i. clarify.
          hexploit match_sem_cast_match; et. i.
          hexploit match_free_list; et. i.
          left. esplits. econs. left. apply plus_one. econs; et.
          right. apply CIH. econs; et.
          clear - NEXT. ginduction k; i; inv NEXT; ss; et. econs.
          econs; et. }
        { i. inv FINALTGT. }
        { right. hexploit match_eval_expr_match; et. i. des.
          hexploit match_sem_cast; et. i. des.
          hexploit match_free_list_match; et. i. des.
          econs. econs. econs; et. }
    + pfold. econs. i. rr.
      unfold safe in *. hexploit SAFESRC. { apply star_refl. }
      i. des. { inv H. } inv H; des; clarify.
      econs.
      * i. inv STEPTGT; des; clarify.
        hexploit match_eval_expr_match; et. i. des.
        hexploit (Clight_eval_expr_determ _ _ _ _ _ _ _ H8 H). i. clarify.
        left. esplits. econs. left. apply plus_one. econs; et.
        right. apply CIH.
        assert (n = n0); clarify. { clear - H10 H11 H0. unfold Cop.sem_switch_arg in *. des_ifs; inv H0; et. }
        econs; et. econs. et.
      * i. inv FINALTGT.
      * right. hexploit match_eval_expr_match; et. i. des.
        econs. econs. econs; et. instantiate (1:=n).
        unfold Cop.sem_switch_arg in *. des_ifs; inv H0; et.
    + pfold. econs. i.
      econs.
      * i. inv STEPTGT; des; clarify.
        left. esplits. econs. left. apply plus_one. econs; et.
        right. apply CIH. econs; et.
      * i. inv FINALTGT.
      * right. econs. econs. econs.
    + pfold. econs. i. rr.
      unfold safe in *. hexploit SAFESRC. { apply star_refl. }
      i. des. { inv H. } inv H; des; clarify.
      econs.
      * i. inv STEPTGT; des; clarify. dup H8.
        eapply find_label_aux2 with (k0 := call_cont k') in H8.
        2:{ clear -NEXT. ginduction NEXT; ss. econs. econs; et. }
        des. rewrite H8 in *. clarify.
        left. esplits. econs. left. apply plus_one. econs; et.
        right. apply CIH. econs; et.
      * i. inv FINALTGT.
      * dup H8.
        eapply find_label_aux2 with (k0 := call_cont k') in H8.
        2:{ clear -NEXT. ginduction NEXT; ss. econs. econs; et. }
        des. right. econs. econs. econs; et.
  - pfold. econs. i. rr.
    unfold safe in *. hexploit SAFESRC. { apply star_refl. }
    i. des. { inv H. } inv H; des; clarify.
    + econs.
      * i. inv STEPTGT; des; clarify.
        hexploit match_function_entry2_match. 2: et. all: et. i. des.
        assert (e = e0 /\ le' = le0 /\ m1' = m2).
        { inv H. inv H5. hexploit alloc_variables_determ. apply H7. apply H11. i. des. clarify. }
        des. clarify.
        left. esplits. econs. left. apply plus_one. econs; et. right. apply CIH. econs; et.
      * i. inv FINALTGT.
      * right. hexploit match_function_entry2_match. 2: et. all: et. i. des.
        econs. econs. econs; et.
    + econs.
      * i. inv STEPTGT.
        destruct (is_external_efb ef) eqn:B.
        { hexploit is_external_ef_reflect. rewrite B. i. inv H.
          hexploit external_call_mem_extends_backward. 3: et. all: et.
          i. des.
          - left. esplits.
            { instantiate (1:=tr'). clear. apply tr_rel_refl. i. rr.
              des_ifs; esplits; et; rr; des_ifs.
              all: induction l; ss; econs; et; unfold evval_rel, eventval_bind; des_ifs. }
            { left. apply plus_one. econs; et. }
            { right. apply CIH. econs; eauto. }
          - exfalso. eapply H. et.
          - right. unfold lib.sflib.NW in *. des.
            esplits; et. { apply star_one. econs; et. }
            rewrite <- H2. apply tr_rel_refl. i. rr.
            des_ifs; esplits; et; rr; des_ifs.
            all: induction l; ss; econs; et; unfold evval_rel, eventval_bind; des_ifs. }
        { hexploit is_external_ef_reflect. rewrite B. i. inv H.
          hexploit external_call_mem_extends. 3: et. all: et. i. des.
          hexploit external_call_determ. et. apply H9. et. i. des. clarify.
          left. esplits.
          { instantiate (1:=t). clear. apply tr_rel_refl. i. rr.
            des_ifs; esplits; et; rr; des_ifs.
            all: induction l; ss; econs; et; unfold evval_rel, eventval_bind; des_ifs. }
          { left. apply plus_one. econs; et. }
          { right. apply CIH. econs; eauto. } }
      * i. inv FINALTGT.
      * right. rr.
        destruct (is_external_efb ef) eqn:B.
        { hexploit is_external_ef_reflect. rewrite B. i. inv H.
          hexploit external_call_mem_extends_backward_progress; eauto.
          i. des. eexists _,_. econs; et. }
        { hexploit is_external_ef_reflect. rewrite B. i. inv H.
          hexploit external_call_mem_extends. 3: et. all: et. i. des.
          eexists _,_. econs; et. }
  - pfold. econs. i. rr.
    econs.
    + i. inv STEPTGT. inv NEXT. left. esplits. econs. left. apply plus_one. econs.
      right. apply CIH. econs; et. ii. destruct optid; ss.
      destruct (Pos.eq_dec i id); clarify. { rewrite ! PTree.gss. et. }
      rewrite ! PTree.gso; et.
    + i. inv FINALTGT. inv VALINJ.
      * inv NEXT. esplits. econs. econs.
      * exfalso. inv NEXT. unfold safe in *.
        hexploit SAFESRC. { apply star_refl. }
        i. des. { inv H. } { inv H. }
    + unfold safe in *. hexploit SAFESRC. { apply star_refl. }
      i. des.
      * inv H. inv NEXT. inv VALINJ. left. econs. econs.
      * inv H. inv NEXT. right. econs. econs. econs.
Qed.

Lemma semantics2to3 p:
  forall obs1, program_observes (Clight.semantics2 p) obs1 ->
  exists obs0, program_observes (semantics3 p) obs0 /\ observation_improves obs0 obs1.
Proof.
  apply backward_simulation_observation_improves.
  econs. econs.
  { apply Arith.Wf_nat.lt_wf. }
  { i. inversion INITSRC. eexists. econs; eauto. }
  i. inv INITSRC. inv INITTGT. inv TGTCAP.
  replace ge0 with ge in * by auto. clear ge0. clarify.
  esplits; ss.
  { econs; eauto. }
  { eauto. ii. unfold concrete_snapshot in *. des_ifs. ss.
    hexploit Genv.init_mem_logical; et. i. rewrite H0 in *. clarify. }
  { eapply match_states_bsim. econs; eauto. 2:econs.
    clear - CAPTURE. inv CAPTURE. revert CAP. generalize (Genv.non_static_glob (Genv.globalenv p) (Genv.genv_public (Genv.globalenv p))).
    i. ginduction l; i; ss. { inv CAP. apply Mem.extends_refl. }
    inv CAP. apply IHl in CAPLIST; et. eapply Mem.extends_extends_compose; et.
    clear - CAP0. inv CAP0. econs; et.
    - econs; unfold inject_id in *.
      + i. clarify. replace (ofs + 0)%Z with ofs by nia. unfold Mem.perm in *. rewrite <- ACCESS. et.
      + i. clarify. exists 0%Z. et.
      + i. clarify. replace (ofs + 0)%Z with ofs by nia. rewrite CONTENTS.
        destruct (ZMap.get _ _); econs. destruct v; econs; ss.
        rewrite Ptrofs.add_zero. et.
    - i. unfold Mem.perm in *. rewrite ACCESS. et.
    - i. destruct (Pos.eq_dec a b); cycle 1; clarify.
      { erewrite <- Mem.concrete_other; et. econs; et. }
      hexploit PREVADDR; et. i. des. rewrite <- H2. et. }
Qed.
