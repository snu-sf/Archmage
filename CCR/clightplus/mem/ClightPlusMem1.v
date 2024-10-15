Require Import CoqlibCCR.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import PCM IPM.
Require Import HoareDef STB.

From compcert Require Import Floats Integers Values Memory AST Ctypes Clight Clightdefs.

Require Import ClightPlusSkel.
Require Import ClightPlusExprgen.
Require Import ClightPlusMemRA.

From stdpp Require Import base.

Set Implicit Arguments.

Local Open Scope Z.

(* zero size allocation is not allowed because there's no guarentee to base address *)
Record metadata := { blk : option block; sz : Z; SZPOS: blk <> None -> 0 < sz }.

Section PRED.

  Context `{@GRA.inG Mem.t Σ}.

  Local Open Scope bi_scope.

  Definition get_align (sz: nat) : Z :=
    if lt_dec sz 2 then 1
    else if le_dec sz 4 then 2
    else if lt_dec sz 8 then 4
    else 8
  .

  (* last offset's physical address and offset should not over ptrofs.max *)
  Definition _has_offset vaddr m ofs : iProp :=
    OwnM (_has_size m.(blk) m.(sz))
    ** match vaddr with
       | Vptr b ofs' => ⌜Some b = m.(blk) /\ ofs = ofs' /\ m.(sz) ≤ Ptrofs.max_unsigned⌝
       | Vint i =>
          if Archi.ptr64 then ⌜False⌝
          else ∃ a, OwnM (_has_base m.(blk) a)
               ** ⌜ofs = Ptrofs.sub (Ptrofs.of_int i) a
                  /\ (Ptrofs.unsigned a = 0%Z -> m.(blk) = None)
                  /\ Ptrofs.unsigned a + m.(sz) ≤ Ptrofs.max_unsigned⌝
       | Vlong i =>
          if negb Archi.ptr64 then ⌜False⌝
          else ∃ a, OwnM (_has_base m.(blk) a)
               ** ⌜ofs = Ptrofs.sub (Ptrofs.of_int64 i) a
                  /\ (Ptrofs.unsigned a = 0%Z -> m.(blk) = None)
                  /\ Ptrofs.unsigned a + m.(sz) ≤ Ptrofs.max_unsigned⌝
       | _ => ⌜False⌝
       end
  .

  Definition equiv_prov vaddr vaddr' m : iProp :=
    ∃ ofs, _has_offset vaddr m ofs ** _has_offset vaddr' m ofs.

  (* also, metadata's size should be upper limit of indicated cell *)
  Definition points_to vaddr m mvs q : iProp :=
    match m.(blk) with
    | None => ⌜False⌝
    | Some blk =>
        OwnM (_has_size (Some blk) m.(sz))
        ** ∃ ofs, OwnM (_points_to blk (Ptrofs.unsigned ofs) mvs q) ** _has_offset vaddr m ofs
        ** ⌜Ptrofs.unsigned ofs + length mvs ≤ m.(sz)⌝
    end%I
  .

  Definition has_offset vaddr m ofs tg q : iProp :=
    match m.(blk) with
    | None => ⌜False⌝
    | Some blk => OwnM(_allocated_with blk tg q) ** _has_offset vaddr m ofs
    end%I
  .

  Definition is_alive m tg q vaddr : iProp := has_offset vaddr m Ptrofs.zero tg q.

  Definition m_null : metadata.
  Proof.
    eapply (@Build_metadata None 0). i. clarify.
  Defined.

  Definition disjoint (m m0: metadata) : Prop :=
    m.(blk) <> m0.(blk).

  Definition valid (m: metadata) (ofs: ptrofs) : Prop :=
    Ptrofs.unsigned ofs < m.(sz).

  Definition weak_valid (m: metadata) (ofs: ptrofs) : Prop :=
    Ptrofs.unsigned ofs ≤ m.(sz).

End PRED.

Notation "vaddr ⊨ m # ofs" := (_has_offset vaddr m ofs) (at level 10).
Notation "vaddr '(↦_' m , q ) mvs" := (points_to vaddr m mvs q) (at level 20).
Notation "vaddr '(⊨_' m , tg , q ) ofs" := (has_offset vaddr m ofs tg q) (at level 10).
Notation "'live_(' m , tg , q ) vaddr" := (is_alive m tg q vaddr) (at level 10).
Notation "m #^ m0" := (disjoint m m0) (at level 20).
Notation "vaddr '(≃_' m ) vaddr'" := (equiv_prov vaddr vaddr' m) (at level 20).

Section AUX.

  Lemma ptrofs_int64_neg i :
    Archi.ptr64 = true -> Ptrofs.neg (Ptrofs.of_int64 i) = Ptrofs.of_int64 (Int64.neg i).
  Proof.
    i. unfold Ptrofs.neg, Ptrofs.of_int64, Int64.neg.
    apply Ptrofs.eqm_samerepr.
    rewrite <- Ptrofs.eqm64; try apply H.
    eapply Int64.eqm_trans.
    2:{ apply Int64.eqm_unsigned_repr. }
    apply Int64.eqm_neg. apply Int64.eqm_sym.
    apply Int64.eqm_unsigned_repr.
  Qed.

  Lemma int64_ptrofs_neg p :
    Archi.ptr64 = true -> Int64.neg (Ptrofs.to_int64 p) = Ptrofs.to_int64 (Ptrofs.neg p).
  Proof.
    i. unfold Ptrofs.neg, Ptrofs.to_int64, Int64.neg.
    apply Int64.eqm_samerepr.
    apply Ptrofs.eqm64; et.
    eapply Ptrofs.eqm_trans.
    2:{ apply Ptrofs.eqm_unsigned_repr. }
    apply Ptrofs.eqm_neg. apply Ptrofs.eqm_sym.
    apply Ptrofs.eqm_unsigned_repr.
  Qed.

  Lemma ptrofs_int64_add i k :
    Archi.ptr64 = true -> Ptrofs.add (Ptrofs.of_int64 i) k = Ptrofs.of_int64 (Int64.add i (Ptrofs.to_int64 k)).
  Proof.
    i. unfold Ptrofs.of_int64, Ptrofs.to_int64, Int64.add, Ptrofs.add.
    rewrite (Int64.unsigned_repr (Ptrofs.unsigned _)).
    2:{ change Int64.max_unsigned with Ptrofs.max_unsigned.
        apply Ptrofs.unsigned_range_2. }
    rewrite (Ptrofs.unsigned_repr (Int64.unsigned _)).
    2:{ change Ptrofs.max_unsigned with Int64.max_unsigned.
        apply Int64.unsigned_range_2. }
    apply Ptrofs.eqm_samerepr.
    rewrite <- Ptrofs.eqm64; et.
    apply Int64.eqm_unsigned_repr.
  Qed.

  Lemma weak_valid_nil_paddr_base a sz :
    Ptrofs.unsigned (Ptrofs.repr (- Ptrofs.unsigned a)) ≤ sz ->
    Ptrofs.unsigned a <> 0 ->
    Ptrofs.unsigned a + sz ≤ Ptrofs.max_unsigned -> False.
  Proof.
    unfold Ptrofs.sub.
    change (Ptrofs.unsigned (Ptrofs.of_int64 _)) with 0%Z.
    rewrite Ptrofs.unsigned_repr_eq. i.
    rewrite Z_mod_nz_opp_full in *.
    2:{ rewrite Z.mod_small; et. destruct a; ss; nia. }
    rewrite Z.mod_small in *. 2:{ destruct a; ss; nia. }
    change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *.
    nia.
  Qed.

  Lemma paddr_no_overflow_cond i a sz:
        Ptrofs.unsigned (Ptrofs.sub (Ptrofs.of_int64 i) a) ≤ sz ->
        Ptrofs.unsigned a + sz ≤ Ptrofs.max_unsigned ->
        0 ≤ Int64.unsigned i - Ptrofs.unsigned a ≤ sz.
  Proof.
    i. unfold Ptrofs.sub, Ptrofs.of_int64 in *.
    rewrite (Ptrofs.unsigned_repr (_ i)) in H.
    2:{ apply Int64.unsigned_range_2. }
    rewrite Ptrofs.unsigned_repr_eq in *.
    destruct (Coqlib.zle 0 (Ptrofs.unsigned a - Int64.unsigned i)).
    { destruct (Coqlib.zeq 0 (Int64.unsigned i - Ptrofs.unsigned a)).
      { rewrite <- e in *. ss. }
      replace (Int64.unsigned i - Ptrofs.unsigned a) with (- (Ptrofs.unsigned a - Int64.unsigned i)) in H by nia.
      rewrite Z_mod_nz_opp_full in *; [>rewrite Z.mod_small in *|rewrite Z.mod_small..]; et.
      all: try apply Ptrofs.unsigned_range; try nia.
      change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in H.
      all: destruct a; destruct i; ss; nia. }
    rewrite Z.mod_small in *.
    2:{ destruct a; destruct i; ss. change Int64.modulus with Ptrofs.modulus in *. nia. }
    nia.
  Qed.

  Lemma paddr_no_overflow_cond_lt i a sz:
        Ptrofs.unsigned (Ptrofs.sub (Ptrofs.of_int64 i) a) < sz ->
        Ptrofs.unsigned a + sz ≤ Ptrofs.max_unsigned ->
        0 ≤ Int64.unsigned i - Ptrofs.unsigned a < sz.
  Proof.
    i. unfold Ptrofs.sub, Ptrofs.of_int64 in *.
    rewrite (Ptrofs.unsigned_repr (_ i)) in H. 2:{ apply Int64.unsigned_range_2. }
    rewrite Ptrofs.unsigned_repr_eq in *.
    destruct (Coqlib.zle 0 (Ptrofs.unsigned a - Int64.unsigned i)); cycle 1.
    { rewrite Z.mod_small in *; try nia.
      destruct a; destruct i; ss. change Int64.modulus with Ptrofs.modulus in *. nia. }
    destruct (Coqlib.zeq 0 (Int64.unsigned i - Ptrofs.unsigned a)). { rewrite <- e in *. ss. }
    replace (Int64.unsigned i - Ptrofs.unsigned a) with (- (Ptrofs.unsigned a - Int64.unsigned i)) in H by nia.
    rewrite Z_mod_nz_opp_full in *; [>rewrite Z.mod_small in *|rewrite Z.mod_small..]; et.
    all: try apply Ptrofs.unsigned_range; try nia.
    change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in H.
    all: destruct a; destruct i; ss; nia.
  Qed.


End AUX.

Section RULES.

  Context `{@GRA.inG Mem.t Σ}.

  Lemma _has_size_dup
      b s :
    OwnM (_has_size b s) ⊢ OwnM (_has_size b s) ** OwnM (_has_size b s).
  Proof.
    iIntros "A".
    set (_has_size _ _) as r at 1.
    replace r with ((_has_size b s) ⋅ (_has_size b s)).
    { iDestruct "A" as "[? ?]". iFrame. }
    unfold r. ur. unfold _has_size, __has_size. rewrite ! URA.unit_id. repeat f_equal.
    ur. extensionalities. des_ifs; ur; des_ifs; et.
  Qed.

  Lemma _has_size_unique
      b s0 s1 :
    OwnM (_has_size b s0 ⋅ _has_size b s1) ⊢ ⌜s0 = s1⌝.
  Proof.
    iIntros "C". iOwnWf "C" as wfc. iPureIntro.
    ur in wfc. des.
    match goal with
    | H : @URA.wf ClightPlusMemRA._blocksizeRA _ |- _ => rename H into X
    end.
    clear -X. ur in X. spc X. unfold __has_size in X. des_ifs; ur in X; des_ifs.
  Qed.

  Lemma _has_base_dup
      b s :
    OwnM (_has_base b s) ⊢ OwnM (_has_base b s) ** OwnM (_has_base b s).
  Proof.
    iIntros "A".
    set (_has_base _ _) as r at 1.
    replace r with ((_has_base b s) ⋅ (_has_base b s)).
    { iDestruct "A" as "[? ?]". iFrame. }
    unfold r. ur. unfold _has_base, __has_base. rewrite ! URA.unit_id. repeat f_equal.
    ur. extensionalities. des_ifs; ur; des_ifs; et.
  Qed.

  Lemma _has_base_unique
      b s0 s1 :
    OwnM (_has_base b s0 ⋅ _has_base b s1) ⊢ ⌜s0 = s1⌝.
  Proof.
    iIntros "C". iOwnWf "C" as wfc. iPureIntro.
    ur in wfc. des.
    match goal with
    | H : @URA.wf ClightPlusMemRA._blockaddressRA _ |- _ => rename H into X
    end.
    clear -X. ur in X. spc X. unfold __has_base in X. des_ifs; ur in X; des_ifs.
  Qed.

  Lemma _has_offset_slide
      vaddr m ofs k :
    vaddr ⊨ m # ofs ⊢ Val.addl vaddr (Vptrofs k) ⊨ m # (Ptrofs.add ofs k).
  Proof.
    iIntros "[S A]". unfold _has_offset. iFrame. des_ifs.
    - iDestruct "A" as (a) "[A %]". des. iExists _. iFrame. iPureIntro. splits; et.
      clarify. rewrite <- Ptrofs.sub_add_l. f_equal. unfold Val.addl, Vptrofs in *.
      des_ifs. rewrite ptrofs_int64_add; et.
    - iDestruct "A" as "%". des. iPureIntro. unfold Val.addl, Vptrofs in *. des_ifs.
      splits; et. f_equal. rewrite Ptrofs.of_int64_to_int64; et.
  Qed.

  Lemma _has_offset_slide_rev
      vaddr m ofs k :
    Val.addl vaddr (Vptrofs k) ⊨ m # (Ptrofs.add ofs k) ⊢ vaddr ⊨ m # ofs.
  Proof.
    iIntros "[S A]". unfold _has_offset. iFrame. des_ifs.
    - iDestruct "A" as (a) "[A %]". des. iExists _. iFrame. iPureIntro. splits; et.
      unfold Val.addl, Vptrofs in *. des_ifs.
      match goal with
      | H : Ptrofs.add _ _ = Ptrofs.sub _ _ |- _ => rename H into X
      end.
      rewrite <- ptrofs_int64_add in X; et. rewrite Ptrofs.sub_add_l in X.
      apply (f_equal (fun x => Ptrofs.add x (Ptrofs.neg k))) in X.
      rewrite ! Ptrofs.add_assoc in X. rewrite ! Ptrofs.add_neg_zero in X.
      rewrite ! Ptrofs.add_zero in X. et.
    - iDestruct "A" as "%". des. unfold Val.addl, Vptrofs in *. des_ifs.
      iPureIntro. splits; et. rewrite Ptrofs.of_int64_to_int64 in *; et.
      assert (X: Ptrofs.add ofs k = Ptrofs.add i0 k).
      { apply Ptrofs.same_if_eq. rewrite Heq0. rewrite Heq. unfold Ptrofs.eq. ss. des_ifs. }
      apply (f_equal (fun x => Ptrofs.add x (Ptrofs.neg k))) in X.
      rewrite ! Ptrofs.add_assoc in X. rewrite ! Ptrofs.add_neg_zero in X.
      rewrite ! Ptrofs.add_zero in X. et.
  Qed.

  Lemma _has_offset_unique
      vaddr m ofs0 ofs1 :
    vaddr ⊨ m # ofs0 ** vaddr ⊨ m # ofs1 ⊢ ⌜ofs0 = ofs1⌝.
  Proof.
    iIntros "[[S A] [S' B]]". des_ifs.
    - iDestruct "A" as (a) "[A %]". iDestruct "B" as (a0) "[B %]".
      des. clarify. iCombine "A B" as "C".
      iOwnWf "C" as wfc. iPureIntro.
      ur in wfc. des.
      match goal with
      | H : @URA.wf ClightPlusMemRA._blockaddressRA _ |- _ => rename H into X
      end. clear - X. ur in X. specialize (X (blk m)). unfold __has_base in X.
      des_ifs; ur in X; des_ifs.
    - iDestruct "A" as "[A %]". iDestruct "B" as "[B %]". des. clarify.
  Qed.

  Lemma _has_offset_dup
      vaddr m ofs :
    vaddr ⊨m# ofs ⊢ vaddr ⊨m# ofs ** vaddr ⊨m# ofs.
  Proof.
    iIntros "[A' A]".
    unfold _has_offset.
    iPoseProof (_has_size_dup with "A'") as "[? ?]".
    des_ifs; try solve [iDestruct "A" as "%"; clarify].
    - iDestruct "A" as (a) "[A %]".
      iPoseProof (_has_base_dup with "A") as "[A B]".
      iFrame. iSplitL "A"; iExists _; iFrame; clarify.
    - iDestruct "A" as "%". iFrame. ss.
  Qed.

  Lemma _has_offset_nooverflow p ofs m : p ⊨m# ofs ⊢ ⌜m.(sz) ≤ Ptrofs.max_unsigned⌝.
  Proof.
    unfold _has_offset. des_ifs; iIntros "[A B]"; clarify.
    - iDestruct "B" as (a) "[B %]". des. iPureIntro. destruct a; ss. nia.
    - iDestruct "B" as "%". des. et.
  Qed.

  Lemma _offset_slide
      vaddr m tg q ofs k :
    vaddr (⊨_ m, tg, q) ofs ⊢ (Val.addl vaddr (Vptrofs k)) (⊨_ m,tg,q) (Ptrofs.add ofs k).
  Proof.
    iIntros "A". unfold has_offset. des_ifs.
    iDestruct "A" as "[? A]". iFrame. iApply _has_offset_slide. et.
  Qed.

  Lemma _offset_slide_rev
      vaddr m tg q ofs k :
    (Val.addl vaddr (Vptrofs k)) (⊨_ m,tg,q) (Ptrofs.add ofs k) ⊢ vaddr (⊨_ m, tg, q) ofs.
  Proof.
    iIntros "A". unfold has_offset. des_ifs.
    iDestruct "A" as "[? A]". iFrame. iApply _has_offset_slide_rev. et.
  Qed.

  Lemma _offset_unique
      vaddr m tg0 tg1 q0 q1 ofs0 ofs1 :
    vaddr (⊨_ m, tg0, q0) ofs0 ** vaddr (⊨_ m, tg1, q1) ofs1 ⊢ ⌜ofs0 = ofs1⌝.
  Proof.
    iIntros "[A B]". unfold has_offset. des_ifs.
    iDestruct "A" as "[_ A]". iDestruct "B" as "[_ B]".
    iCombine "A B" as "C". iApply _has_offset_unique; et.
  Qed.

  Lemma _offset_trivial
      b m tg q ofs0 ofs1 :
    Vptr b ofs0 (⊨_ m, tg, q) ofs1 ⊢ ⌜m.(blk) = Some b /\ ofs0 = ofs1⌝.
  Proof.
    iIntros "A". unfold has_offset. des_ifs.
    iDestruct "A" as "[_ A]". unfold _has_offset.
    iDestruct "A" as "[_ %]". des. iPureIntro. clarify. split; et. symmetry. etrans; et.
  Qed.

  Lemma _offset_unique_meta
      vaddr m0 m1 tg0 tg1 q0 q1 ofs0 ofs1 :
    vaddr (⊨_ m0, tg0, q0) ofs0 ** vaddr (⊨_ m1, tg1, q1) ofs1 ** ⌜valid m0 ofs0 /\ valid m1 ofs1⌝ ⊢ ⌜m0 = m1⌝.
  Proof.
    iIntros "[[A B] %]". rename H0 into X. unfold has_offset. des_ifs. unfold _has_offset.
    iDestruct "A" as "[Aa [As A]]". iDestruct "B" as "[Ba [Bs B]]". des_ifs; cycle 1.
    - iDestruct "A" as "%". iDestruct "B" as "%". des.
      rewrite <- H0. rewrite <- H1. iCombine "As Bs" as "C".
      iPoseProof (_has_size_unique with "C") as "%". destruct m1. destruct m0. ss. clarify.
      rewrite (proof_irr SZPOS0 SZPOS1). et.
    - iDestruct "A" as (a) "[Ac %]". iDestruct "B" as (a0) "[Bc %]". des.
      rewrite Heq. rewrite Heq0.
      destruct (Pos.eq_dec b b0).
      + clarify. iCombine "As Bs" as "C".
        iPoseProof (_has_size_unique with "C") as "%". destruct m1. destruct m0. ss. clarify.
        rewrite (proof_irr SZPOS0 SZPOS1). et.
      + unfold _allocated_with, _has_size, _has_base, __allocated_with.
        iCombine "Aa As Ac Ba Bs Bc" as "C". ur. rewrite ! URA.unit_idl.
        ur. des_ifs. assert (f0 = fun _ => Consent.unit). { inv Heq3. extensionalities. ss. }
        clarify. iOwnWf "C" as wf. des. ur in wf. des.
        clear wf wf0 wf1 wf2 wf4. hexploit wf3; et.
        { instantiate (1:= sz m0). destruct m0. ss. hexploit SZPOS0; try nia. clarify. }
        { instantiate (1:= sz m1). destruct m1. ss. hexploit SZPOS0; try nia. clarify. }
        { des_ifs. ur. et. }
        { clear wf3. des_ifs. }
        { clear wf3. instantiate (1:= a). des_ifs. }
        { des_ifs. ur. et. }
        { clear wf3. des_ifs. }
        { clear wf3. instantiate (1:= a0). des_ifs. }
        i. clear wf3. exfalso. unfold valid in *. clear - X X0 H0 H5 H3.
        apply paddr_no_overflow_cond_lt in X; et. apply paddr_no_overflow_cond_lt in X0; et. nia.
  Qed.

  Lemma live_offset_exchage
      vaddr m tg q k :
    live_(m, tg, q) (Val.subl vaddr (Vptrofs k)) ⊢ vaddr (⊨_ m, tg, q) k.
  Proof.
    iIntros "A". unfold is_alive. iApply _offset_slide_rev.
    instantiate (1:= (Ptrofs.neg k)). rewrite Ptrofs.add_neg_zero.
    replace (Val.addl _ _) with (Val.subl vaddr (Vptrofs k)); et.
    unfold Vptrofs. des_ifs. rewrite Val.subl_addl_opp. do 2 f_equal.
    apply int64_ptrofs_neg; et.
  Qed.

  Lemma live_offset_exchage_rev
      vaddr m tg q k :
    vaddr (⊨_ m, tg, q) k ⊢ live_(m, tg, q) (Val.subl vaddr (Vptrofs k)).
  Proof.
    iIntros "A". unfold is_alive. iPoseProof (_offset_slide with "A") as "A".
    instantiate (1:= (Ptrofs.neg k)). rewrite Ptrofs.add_neg_zero.
    replace (Val.addl _ _) with (Val.subl vaddr (Vptrofs k)); et.
    unfold Vptrofs. des_ifs. rewrite Val.subl_addl_opp. do 2 f_equal.
    apply int64_ptrofs_neg; et.
  Qed.

  Lemma live_has_offset_ofs
      vaddr m tg q k :
    live_(m, tg, q) (Val.subl vaddr (Vptrofs k)) ⊢ live_(m, tg, q) (Val.subl vaddr (Vptrofs k)) ** vaddr ⊨ m # k.
  Proof.
    unfold is_alive, has_offset. iIntros "A"; des_ifs.
    iDestruct "A" as "[A A']".
    iPoseProof (_has_offset_dup with "A'") as "[A' A'']".
    iFrame. iApply _has_offset_slide_rev. rewrite Ptrofs.add_neg_zero.
    unfold Val.subl, Val.addl. des_ifs.
    - unfold Vptrofs in *. des_ifs. rewrite <- int64_ptrofs_neg; et. rewrite Int64.sub_add_opp. et.
    - unfold Vptrofs in *. des_ifs. rewrite !Ptrofs.of_int64_to_int64; et.
      rewrite Ptrofs.sub_add_opp. et.
  Qed.

  Lemma live_has_offset
      vaddr m tg q :
    live_(m, tg, q) vaddr ⊢ live_(m, tg, q) vaddr ** vaddr ⊨ m # Ptrofs.zero.
  Proof.
    unfold is_alive, has_offset. iIntros "A"; des_ifs.
    iDestruct "A" as "[A A']".
    iPoseProof (_has_offset_dup with "A'") as "[A' A'']".
    iFrame.
  Qed.

  Lemma live_slide
      vaddr m tg q k :
    live_(m, tg, q) vaddr ⊢ live_(m, tg, q) (Val.subl (Val.addl vaddr (Vptrofs k)) (Vptrofs k)).
  Proof.
    iIntros "A". iApply live_offset_exchage_rev. set k at 1.
    rewrite <- (Ptrofs.add_zero_l k). unfold i. clear i.
    iApply _offset_slide. et.
  Qed.

  Lemma live_slide_rev
      vaddr m tg q k :
    live_(m, tg, q) (Val.subl (Val.addl vaddr (Vptrofs k)) (Vptrofs k)) ⊢ live_(m, tg, q) vaddr.
  Proof.
    iIntros "A". iPoseProof (live_offset_exchage with "A") as "A". set k at 1.
    rewrite <- (Ptrofs.add_zero_l k). unfold i. clear i.
    iPoseProof (_offset_slide_rev with "A") as "A". et.
  Qed.

  Lemma live_unique
      vaddr m tg0 tg1 q0 q1 ofs0 ofs1 :
    live_( m, tg0, q0) (Val.subl vaddr (Vptrofs ofs0)) ** live_( m, tg1, q1) (Val.subl vaddr (Vptrofs ofs1)) ⊢ ⌜ofs0 = ofs1⌝.
  Proof.
    iIntros "[A B]".
    iPoseProof (live_offset_exchage with "A") as "A".
    iPoseProof (live_offset_exchage with "B") as "B".
    iApply _offset_unique; iFrame.
  Qed.

  Lemma live_trivial
      b m tg q ofs0 ofs1 :
    live_( m, tg, q) (Val.subl (Vptr b ofs0) (Vptrofs ofs1)) ⊢ ⌜m.(blk) = Some b /\ ofs0 = ofs1⌝.
  Proof.
    iIntros "A". iPoseProof (live_offset_exchage with "A") as "A".
    iApply _offset_trivial; iFrame.
  Qed.

  Lemma live_unique_meta
      vaddr m0 m1 tg0 tg1 q0 q1 ofs0 ofs1 :
    live_( m0, tg0, q0) (Val.subl vaddr (Vptrofs ofs0)) ** live_( m1, tg1, q1) (Val.subl vaddr (Vptrofs ofs1)) ** ⌜valid m0 ofs0 /\ valid m1 ofs1⌝ ⊢ ⌜m0 = m1⌝.
  Proof.
    iIntros "[[A B] %]".
    iPoseProof (live_offset_exchage with "A") as "A".
    iPoseProof (live_offset_exchage with "B") as "B".
    iApply _offset_unique_meta; iFrame. et.
  Qed.

  Lemma _points_to_ownership
      b ofs mvs q0 q1 :
    _points_to b ofs mvs (q0 + q1) = (_points_to b ofs mvs q0) ⋅ (_points_to b ofs mvs q1).
  Proof.
    unfold _points_to. ur. rewrite ! URA.unit_id. repeat f_equal.
    unfold Auth.white. ur. f_equal. extensionalities. ur. ur.
    unfold __points_to. des_ifs; ur; des_ifs.
  Qed.

  Lemma points_to_ownership
      vaddr mvs m q0 q1 :
    ⊢ vaddr (↦_ m, q0 + q1) mvs ∗-∗ (vaddr (↦_ m, q0) mvs ** vaddr (↦_ m, q1) mvs).
  Proof.
    iIntros. iSplit.
    - iIntros "A". unfold points_to.
      destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
      iDestruct "A" as "[B A]".
      iPoseProof (_has_size_dup with "B") as "[? ?]". iFrame.
      iDestruct "A" as (ofs) "[[B A] %]".
      rewrite _points_to_ownership. iDestruct "B" as "[B ?]".
      iPoseProof (_has_offset_dup with "A") as "[A ?]".
      iSplitL "A B"; iExists _; iFrame; et.
    - iIntros "A". unfold points_to.
      iDestruct "A" as "[B A]".
      destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
      iDestruct "A" as "[? A]". iDestruct "B" as "[? B]". iFrame.
      iDestruct "A" as (ofs) "[[A A'] %]". iDestruct "B" as (ofs0) "[[B B'] %]". iCombine "B A" as "C". iCombine "A' B'" as "C'".
      iPoseProof (_has_offset_unique with "C'") as "%". iDestruct "C'" as "[_ C']". clarify.
      iExists _. rewrite _points_to_ownership. iFrame. et.
  Qed.

  Lemma _allocated_with_ownership
      b tg q0 q1 :
    _allocated_with b tg (q0 + q1) = (_allocated_with b tg q0) ⋅ (_allocated_with b tg q1).
  Proof.
    unfold _allocated_with. ur. rewrite ! URA.unit_id. repeat f_equal.
    unfold Auth.white. ur. f_equal. extensionalities. ur.
    unfold __allocated_with. des_ifs; ur; des_ifs.
  Qed.

  Lemma _offset_ownership
      vaddr m tg q0 q1 ofs :
    ⊢ vaddr (⊨_ m, tg, (q0 + q1)%Qp) ofs  ∗-∗ (vaddr (⊨_ m, tg, q0) ofs ** vaddr (⊨_ m, tg, q1) ofs).
  Proof.
    iIntros. iSplit.
    - iIntros "A". unfold has_offset.
      destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
      rewrite _allocated_with_ownership.
      iDestruct "A" as "[[? ?] A]".
      iPoseProof (_has_offset_dup with "A") as "[? ?]".
      iFrame.
    - iIntros "A". unfold has_offset.
      iDestruct "A" as "[A B]".
      destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
      iDestruct "A" as "[A ?]".
      iDestruct "B" as "[B ?]".
      iCombine "A B" as "?".
      rewrite _allocated_with_ownership. iFrame.
  Qed.

  Lemma live_ownership
      vaddr m tg q0 q1 :
    ⊢ live_(m, tg, (q0 + q1)%Qp) vaddr ∗-∗ (live_( m, tg, q0) vaddr ** live_( m, tg, q1) vaddr).
  Proof. apply _offset_ownership. Qed.

  Lemma _points_to_nil : forall blk ofs q _b _ofs, __points_to blk ofs [] q _b _ofs = ε.
  Proof.
    intros. unfold __points_to. destruct Pos.eq_dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss.
    des_ifs. destruct (Z.to_nat _); ss.
  Qed.

  Lemma points_to_nil : forall blk ofs q, __points_to blk ofs [] q = ε.
  Proof. i. extensionalities. rewrite _points_to_nil. et. Qed.

  Lemma _points_to_content
      b ofs mvs0 mvs1 q :
    _points_to b ofs (mvs0 ++ mvs1) q = (_points_to b ofs mvs0 q) ⋅ (_points_to b (ofs + length mvs0) mvs1 q).
  Proof.
    unfold _points_to. ur. rewrite ! URA.unit_id. repeat f_equal.
    unfold Auth.white. ur. f_equal. extensionalities. ur. ur.
    unfold __points_to.
    destruct Pos.eq_dec; ur; et; ss;
    destruct Coqlib.zle; ur; et; ss;
    destruct Coqlib.zlt; ur; et; ss;
    try destruct Coqlib.zle; ss;
    try destruct Coqlib.zlt; ss;
    try destruct Coqlib.zlt; ss;
    des_ifs; try rewrite app_length in *; try nia;
    try solve [rewrite nth_error_app1 in *; try nia; clarify
              |rewrite nth_error_app2 in *; try nia;
               replace (Z.to_nat _) with ((Z.to_nat (H1 - ofs)) - length mvs0)%nat in * by nia;
               clarify].
  Qed.

  Lemma points_to_split
      vaddr mvs0 mvs1 m q :
    vaddr (↦_m,q) (mvs0 ++ mvs1) ⊢ vaddr (↦_m,q) mvs0 ** (Val.addl vaddr (Vptrofs (Ptrofs.repr (length mvs0))) (↦_m,q) mvs1).
  Proof.
    iIntros "A". unfold points_to.
    destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
    iDestruct "A" as "[B A]".
    iPoseProof (_has_size_dup with "B") as "[? ?]". iFrame.
    iDestruct "A" as (ofs) "[[B A] %]". rewrite _points_to_content.
    iPoseProof (_has_offset_dup with "A") as "[? A]". iDestruct "B" as "[? B]".
    match goal with
    | H : Ptrofs.unsigned _ + Z.of_nat (length _) <= _ |- _ => rename H into X
    end.
    rewrite app_length in X. iSplitR "A B"; iExists _; iFrame; [iPureIntro; nia|].
    iPoseProof (_has_offset_nooverflow with "A") as "%".
    assert (Y: Ptrofs.unsigned ofs + length mvs0 = Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (length mvs0)))); cycle 1.
    { rewrite Y. iFrame. iSplit. { iApply _has_offset_slide. et. } iPureIntro. nia. }
    unfold Ptrofs.add. destruct ofs. ss.
    rewrite (Ptrofs.unsigned_repr (length _)); try nia.
    rewrite (Ptrofs.unsigned_repr); et. nia.
  Qed.

  Lemma points_to_collect
      vaddr mvs0 mvs1 m q :
    vaddr (↦_m,q) mvs0 ** (Val.addl vaddr (Vptrofs (Ptrofs.repr (Z.of_nat (List.length mvs0)))) (↦_m,q) mvs1) ⊢ vaddr (↦_m,q) (mvs0 ++ mvs1).
  Proof.
    iIntros "[A B]". unfold points_to.
    destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
    iDestruct "A" as "[? A]". iDestruct "B" as "[? B]". iFrame.
    iDestruct "A" as (ofs) "[[A A'] %]". iDestruct "B" as (ofs0) "[[B B'] %]".
    iPoseProof (_has_offset_nooverflow with "A'") as "%".
    iPoseProof (_has_offset_dup with "A'") as "[? A']".
    iPoseProof (_has_offset_slide with "A'") as "A'".
    iCombine "A' B'" as "C'". iCombine "A B" as "C".
    iPoseProof (_has_offset_unique with "C'") as "%". clarify.
    iDestruct "C'" as "[A' B']".
    assert (X: Ptrofs.unsigned ofs + length mvs0 = Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (length mvs0)))); cycle 1.
    { rewrite <- X. rewrite <- _points_to_content. iExists _. iFrame. iPureIntro. rewrite app_length. nia. }
    unfold Ptrofs.add. destruct ofs. ss.
    rewrite (Ptrofs.unsigned_repr (length _)); try nia.
    rewrite (Ptrofs.unsigned_repr); et. nia.
  Qed.

  Lemma points_to_unique_meta
      vaddr m0 m1 q0 q1 mvs0 mvs1 :
    vaddr (↦_m0,q0) mvs0 ** vaddr (↦_m1,q1) mvs1 ** ⌜0 < length mvs0 /\ 0 < length mvs1⌝ ⊢ ⌜m0 = m1⌝.
  Proof.
    iIntros "[[A B] %]". rename H0 into X. unfold points_to. des_ifs.
    iDestruct "A" as "[_ A]". iDestruct "B" as "[_ B]".
    iDestruct "A" as (ofs) "[[Ap [As A]] %]". iDestruct "B" as (ofs0) "[[Bp [Bs B]] %]".
    des_ifs; cycle 1.
    - iDestruct "A" as "%". iDestruct "B" as "%". des.
      rewrite <- H2. rewrite <- H3. iCombine "As Bs" as "C".
      iPoseProof (_has_size_unique with "C") as "%". destruct m1. destruct m0. ss. clarify.
      rewrite (proof_irr SZPOS0 SZPOS1). et.
    - iDestruct "A" as (a) "[Ac %]". iDestruct "B" as (a0) "[Bc %]". des.
      rewrite Heq. rewrite Heq0.
      destruct (Pos.eq_dec b b0).
      + clarify. iCombine "As Bs" as "C".
        iPoseProof (_has_size_unique with "C") as "%". destruct m1. destruct m0. ss. clarify.
        rewrite (proof_irr SZPOS0 SZPOS1). et.
      + unfold _points_to, _has_size, _has_base, __points_to.
        assert (exists x0, hd_error mvs0 = Some x0). { destruct mvs0; ss; et. }
        assert (exists x1, hd_error mvs1 = Some x1). { destruct mvs1; ss; et. }
        iCombine "Ap As Ac Bp Bs Bc" as "C". ur. rewrite ! URA.unit_idl. rewrite ! URA.unit_id.
        ur. clarify. iOwnWf "C" as wf. des. ur in wf. des.
        clear wf wf0 wf1 wf2 wf3. hexploit wf4; et; clear wf4.
        { instantiate (1:=sz m0). instantiate (1:=Ptrofs.unsigned (Ptrofs.sub (Ptrofs.of_int64 i) a)). destruct m0, Ptrofs.sub. ss. hexploit SZPOS0; clarify. nia. }
        { instantiate (1:=sz m1). instantiate (1:=Ptrofs.unsigned (Ptrofs.sub (Ptrofs.of_int64 i) a0)). destruct m1, (Ptrofs.sub _ a0). ss. hexploit SZPOS0; clarify. nia. }
        { ur. destruct Pos.eq_dec; destruct Coqlib.zle; destruct Coqlib.zlt; ss; try nia.
          destruct Pos.eq_dec; ss. replace (Z.to_nat _) with 0%nat by nia. destruct mvs0; ss.
          ur. clarify. }
        { des_ifs. }
        { instantiate (1:=a). des_ifs. }
        { ur. destruct Pos.eq_dec at 2; destruct Coqlib.zle at 2; destruct Coqlib.zlt at 2; ss; try nia.
          destruct Pos.eq_dec; clarify; ss. replace (Z.to_nat _) with 0%nat by nia. destruct mvs1; ss.
          ur. clarify. }
        { des_ifs. }
        { instantiate (1:=a0). des_ifs. }
        i. exfalso. hexploit (paddr_no_overflow_cond_lt i); et; try nia. move H7 at bottom.
        hexploit (paddr_no_overflow_cond_lt i); et; try nia.
  Qed.
  
  Lemma points_to_trivial
      b m q ofs mvs :
    (Vptr b ofs) (↦_m,q) mvs ⊢ ⌜m.(blk) = Some b⌝.
  Proof.
    iIntros "A". unfold points_to. des_ifs.
    iDestruct "A" as "(A & B)".
    iDestruct "B" as (ofs0) "((B & C) & D)".
    unfold _has_offset.
    iDestruct "C" as "(C & %)". des. clarify.
    rewrite <- Heq. rewrite H0. et.
  Qed.

  Lemma equiv_refl_point
      m p q mvs :
    p (↦_m,q) mvs  ⊢  p (↦_m,q) mvs ** p (≃_m) p.
  Proof.
    iIntros "A". unfold points_to.
    destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
    iDestruct "A" as "[? A]". iDestruct "A" as (ofs) "[[B A] %]".
    iFrame. iPoseProof (_has_offset_dup with "A") as "[? A]".
    iPoseProof (_has_offset_dup with "A") as "[? A]".
    iSplitL "A B"; iExists _; iFrame. et.
  Qed.

  Lemma _equiv_refl_offset
      m p tg q ofs :
    p (⊨_m,tg,q) ofs  ⊢  p (⊨_m,tg,q) ofs ** p (≃_m) p.
  Proof.
    iIntros "A". unfold has_offset.
    destruct (blk m); try solve [iDestruct "A" as "%"; clarify].
    iDestruct "A" as "[? A]".
    iPoseProof (_has_offset_dup with "A") as "[? A]".
    iPoseProof (_has_offset_dup with "A") as "A".
    iSplitR "A"; iFrame. iExists _. et.
  Qed.

  Lemma equiv_refl_live
      m p tg q :
    live_(m,tg,q) p ⊢ live_(m,tg,q) p ** p (≃_m) p.
  Proof. apply _equiv_refl_offset. Qed.

  Lemma _equiv_trivial_offset
      m p tg q ofs b
      (BLK: blk m = Some b) :
    p (⊨_m,tg,q) ofs  ⊢ (Vptr b ofs) (⊨_m,tg,q) ofs ** p (≃_m) (Vptr b ofs).
  Proof.
    iIntros "A". unfold has_offset.
    destruct (blk m) eqn:?; try solve [iDestruct "A" as "%"; clarify]. clarify.
    iDestruct "A" as "[? A]". iFrame.
    unfold equiv_prov.
    iPoseProof (_has_offset_dup with "A") as "[A B]".
    iPoseProof (_has_offset_dup with "B") as "[B C]".
    iSplitL "A".
    - unfold _has_offset. iDestruct "A" as "[A B]".
      des_ifs; clarify.
      + iDestruct "B" as (a) "[B %]". des. clarify. iFrame. iPureIntro. splits; et.
        destruct a; ss; nia.
      + iFrame. rewrite Heqo. iDestruct "B" as "%". des. et.
    - iExists _. iFrame.
      unfold _has_offset. iDestruct "B" as "[A B]".
      des_ifs; clarify.
      + iDestruct "B" as (a) "[B %]". des. clarify. iFrame. iPureIntro. splits; et.
        destruct a; ss; nia.
      + iFrame. rewrite Heqo. iDestruct "B" as "%". des. et.
  Qed.

  Lemma live_trivial_offset
      m p tg q b
      (BLK: blk m = Some b) :
    live_(m,tg,q) p ⊢ live_(m,tg,q) (Vptr b Ptrofs.zero) ** p (≃_m) (Vptr b Ptrofs.zero).
  Proof. apply _equiv_trivial_offset; et. Qed.

  Lemma equiv_refl_equiv
      m p q :
    p (≃_m) q ⊢ p (≃_m) p.
  Proof.
    iIntros "A". unfold equiv_prov.
    iDestruct "A" as (ofs) "[A _]".
    iPoseProof (_has_offset_dup with "A") as "[? ?]".
    iExists _. iFrame.
  Qed.

  Lemma equiv_sym
      p q m :
    p (≃_m) q ⊢ q (≃_m) p.
  Proof.
    iIntros "A". unfold equiv_prov.
    iDestruct "A" as (ofs) "[A B]".
    iExists ofs. iFrame.
  Qed.

  Lemma equiv_trans
      p q r m :
    p (≃_m) q ** q (≃_m) r ⊢ p (≃_m) r.
  Proof.
    iIntros "A". unfold equiv_prov.
    iDestruct "A" as "[A B]".
    iDestruct "A" as (ofs1) "[A A']". iDestruct "B" as (ofs2) "[B B']".
    iCombine "A' B" as "A'". iPoseProof (_has_offset_unique with "A'") as "%". subst.
    iExists ofs2. iFrame.
  Qed.

  Lemma equiv_dup
      p q m :
    p (≃_m) q ⊢ p (≃_m) q ** p (≃_m) q.
  Proof.
    unfold equiv_prov.
    iIntros "A".
    iDestruct "A" as (ofs) "[A B]".
    iPoseProof (_has_offset_dup with "A") as "[A ?]".
    iPoseProof (_has_offset_dup with "B") as "[B ?]".
    iSplitL "A B"; iExists _; iFrame.
  Qed.

  Lemma equiv_slide
      p q m k :
    p (≃_m) q ⊢ (Val.addl p (Vptrofs k)) (≃_m) (Val.addl q (Vptrofs k)).
  Proof.
    iIntros "A". iDestruct "A" as (ofs) "[A A']".
    iExists _. iSplitL "A"; iApply _has_offset_slide; et.
  Qed.

  Lemma equiv_slide_rev
      p q m k :
    (Val.addl p (Vptrofs k)) (≃_m) (Val.addl q (Vptrofs k)) ⊢ p (≃_m) q.
  Proof.
    iIntros "A". iDestruct "A" as (ofs) "[A A']".
    replace ofs with (Ptrofs.add (Ptrofs.add ofs (Ptrofs.neg k)) k).
    2:{ rewrite Ptrofs.add_assoc. rewrite (Ptrofs.add_commut (Ptrofs.neg _)).
        rewrite Ptrofs.add_neg_zero. rewrite Ptrofs.add_zero. et. }
    iExists _. iSplitL "A"; iApply _has_offset_slide_rev; et.
  Qed.

  Lemma capture_unique
      p m i j :
    p (≃_m) (Vptrofs i) ** p (≃_m) (Vptrofs j) ⊢ ⌜i = j⌝.
  Proof.
    iIntros "[A B]".
    iDestruct "A" as (ofs0) "[A' A]".
    iDestruct "B" as (ofs1) "[B' B]".
    iCombine "A' B'" as "C".
    iPoseProof (_has_offset_unique with "C") as "%". clarify. iClear "C".
    unfold _has_offset. des_ifs.
    iDestruct "A" as "[_ A]".
    iDestruct "B" as "[_ B]".
    iDestruct "A" as (a0) "[A %]".
    iDestruct "B" as (a1) "[B %]".
    iCombine "A B" as "C".
    iPoseProof (_has_base_unique with "C") as "%". clarify.
    iPureIntro.
    assert (i0 = i1).
    { des. rewrite H0 in H1. clear - H1.
      assert (Ptrofs.eq (Ptrofs.sub (Ptrofs.of_int64 i0) a1) (Ptrofs.sub (Ptrofs.of_int64 i1) a1) = true).
      { rewrite H1. apply Ptrofs.eq_true. }
      do 2 rewrite Ptrofs.sub_add_opp in H.
      rewrite Ptrofs.translate_eq in H.
      apply Ptrofs.same_if_eq in H.
      apply (f_equal Ptrofs.to_int64) in H.
      rewrite Ptrofs.to_int64_of_int64 in H; et.
      rewrite Ptrofs.to_int64_of_int64 in H; et. }
    subst. rewrite <- Heq in Heq1.
    clear -Heq1. unfold Vptrofs in *. destruct Archi.ptr64 eqn:?. 2:{ clarify. }
    apply (f_equal (fun v => match v with Vlong i => i | _ => Int64.zero end)) in Heq1.
    apply (f_equal Ptrofs.of_int64) in Heq1.
    rewrite Ptrofs.of_int64_to_int64 in Heq1; et.
    rewrite Ptrofs.of_int64_to_int64 in Heq1; et.
  Qed.

  Lemma _ii_offset_eq
      i j ofs m :
    Vptrofs i ⊨ m # ofs ** Vptrofs j ⊨ m # ofs ⊢ ⌜i = j⌝.
  Proof.
    iIntros "[A B]".
    unfold _has_offset. des_ifs.
    iDestruct "A" as "[_ A]".
    iDestruct "B" as "[_ B]".
    iDestruct "A" as (a) "[A %]".
    iDestruct "B" as (a') "[B %]".
    iCombine "A B" as "C". iOwnWf "C" as wfc.
    iPureIntro. ur in wfc. des.
    match goal with
    | H : @URA.wf ClightPlusMemRA._blockaddressRA _ |- _ => rename H into X
    end. ur in X. specialize (X (blk m)). clear wfc3 wfc4. unfold __has_base in X.
    assert (a = a'). { des_ifs; ur in X; des_ifs. }
    clarify. clear X. unfold Vptrofs in *. des_ifs.
    rewrite Ptrofs.of_int64_to_int64 in *; et.
    assert (X: Ptrofs.sub j a' = Ptrofs.sub i a').
    { apply Ptrofs.same_if_eq. rewrite Heq3. rewrite Heq2. unfold Ptrofs.eq. ss. des_ifs. }
    apply (f_equal ((flip Ptrofs.add) a')) in X. ss.
    rewrite ! Ptrofs.sub_add_opp in X. rewrite ! Ptrofs.add_assoc in X.
    rewrite ! (Ptrofs.add_commut _ a') in X. rewrite ! Ptrofs.add_neg_zero in X.
    rewrite ! Ptrofs.add_zero in X. et.
  Qed.

  Lemma equiv_ii_eq
      i j m :
    Vptrofs i (≃_m) Vptrofs j ⊢ ⌜i = j⌝.
  Proof.
    iIntros "A".
    iDestruct "A" as (ofs) "A".
    iApply _ii_offset_eq. et.
  Qed.

  Lemma equiv_point_comm
      p q f m mvs :
    p (≃_m) q ** p (↦_m,f) mvs ⊢ q (↦_m,f) mvs.
  Proof.
    iIntros "[A B]". unfold equiv_prov. iDestruct "A" as (ofs) "[A A']".
    unfold points_to.
    destruct (blk m); try solve [iDestruct "B" as "[]"].
    iDestruct "B" as "[? B]". iFrame.
    iDestruct "B" as (ofs0) "[[P B] %]".
    iCombine "A B" as "C".
    iPoseProof (_has_offset_unique with "C") as "%". subst.
    iPoseProof (_has_offset_dup with "A'") as "[A' B']".
    iDestruct "C" as "[_ A]".
    iExists _. iFrame. et.
  Qed.

  Lemma _equiv_has_offset_comm
      p q m ofs :
    p (≃_m) q ** p ⊨ m # ofs ⊢ q ⊨ m # ofs.
  Proof.
    iIntros "[A B]". unfold equiv_prov. iDestruct "A" as (ofs0) "[A A']".
    iCombine "A B" as "C".
    iPoseProof (_has_offset_unique with "C") as "%".
    clarify.
  Qed.

  Lemma _equiv_offset_comm
      p q tg f m ofs :
    p (≃_m) q ** p (⊨_m,tg,f) ofs ⊢ q (⊨_m,tg,f) ofs.
  Proof.
    iIntros "[A B]".
    unfold equiv_prov.
    iDestruct "A" as (ofs0) "[A A']".
    unfold has_offset. des_ifs.
    iDestruct "B" as "[? B]".
    iFrame. iCombine "A B" as "C".
    iPoseProof (_has_offset_unique with "C") as "%".
    clarify.
  Qed.

  Lemma equiv_live_comm
      p q tg f m :
    p (≃_m) q ** live_(m,tg,f) p ⊢ live_(m,tg,f) q.
  Proof. apply _equiv_offset_comm. Qed.

  Lemma equiv_live_comm_ofs
      p q tg f m k :
    p (≃_m) q ** live_(m,tg,f) (Val.subl p (Vptrofs k)) ⊢ live_(m,tg,f) (Val.subl q (Vptrofs k)).
  Proof.
    iIntros "[A B]".
    iApply live_offset_exchage_rev.
    iApply _equiv_offset_comm. iFrame.
    iApply live_offset_exchage. iFrame.
  Qed.

  Lemma null_equiv p : Vnullptr (≃_m_null) p ⊢ ⌜p = Vnullptr⌝.
  Proof.
    iIntros "A".
    destruct p;
      try solve [iDestruct "A" as (ofs) "[_ A]"; iDestruct "A" as "[? []]"].
    - change Vnullptr with (Vptrofs Ptrofs.zero).
      replace (Vlong i) with (Vptrofs (Ptrofs.of_int64 i)).
      2:{ unfold Vptrofs. des_ifs. f_equal. apply Ptrofs.to_int64_of_int64; et. }
      iPoseProof (equiv_ii_eq with "A") as "%". rewrite H0. et.
    - iDestruct "A" as (ofs) "[_ [_ %]]". des. clarify.
  Qed.

  Lemma equiv_notundef
      p q m :
    p (≃_m) q ⊢ ⌜p <> Vundef⌝.
  Proof.
    iIntros "A".
    destruct p;
      try solve [iDestruct "A" as (ofs) "[A _]"; iDestruct "A" as "[? []]"].
    all : iPureIntro; ss.
  Qed.

  Lemma point_notnull
      vaddr m q mvs :
    vaddr (↦_m,q) mvs ⊢ ⌜vaddr <> Vnullptr⌝.
  Proof.
    iIntros "A". unfold points_to. des_ifs.
    iDestruct "A" as "[_ A]".
    iDestruct "A" as (ofs) "[[_ A] %]".
    unfold _has_offset. des_ifs.
    iDestruct "A" as "[_ A]".
    iDestruct "A" as (a) "[A %]".
    iPureIntro. des. clarify.
    assert (X: i <> Int64.zero); try solve [red; intro X'; apply X; inv X'; ss].
    red. i. subst. unfold Ptrofs.sub in *.
    change (Ptrofs.unsigned (Ptrofs.of_int64 Int64.zero)) with 0%Z in *.
    rewrite Ptrofs.unsigned_repr_eq in *.
    destruct (Coqlib.zeq 0 (Ptrofs.unsigned a)). { rewrite H2 in *; et. clarify. }
    rewrite Z_mod_nz_opp_full in H0. 2: rewrite Z.mod_small; et; apply Ptrofs.unsigned_range.
    rewrite Z.mod_small in *. 2: apply Ptrofs.unsigned_range.
    change Ptrofs.modulus with (Ptrofs.max_unsigned + 1) in *. nia.
  Qed.

  Lemma live_notnull_ofs
      vaddr m tg q ofs
      (WEAK: weak_valid m ofs):
    live_(m,tg,q) (Val.subl vaddr (Vptrofs ofs)) ⊢ ⌜vaddr <> Vnullptr⌝.
  Proof.
    iIntros "A". unfold is_alive, has_offset. des_ifs.
    iDestruct "A" as "[_ A]". iDestruct "A" as "[_ A]".
    unfold _has_offset. des_ifs.
    - iDestruct "A" as (a) "[A %]". des. iPureIntro. ii. clarify.
      unfold weak_valid in WEAK.
      hexploit paddr_no_overflow_cond; et.
      { rewrite <- H0. destruct ofs; ss. change (Ptrofs.unsigned Ptrofs.zero) with 0. nia. }
      i. rewrite H1 in Heq; clarify. 
      unfold Vnullptr, Vptrofs in Heq0. des_ifs. ss.
      inv Heq0. unfold Int64.sub in H3.
      change (Int64.unsigned Int64.zero) with 0 in H3.
      unfold Ptrofs.to_int64 in H3. rewrite (Int64.unsigned_repr (Ptrofs.unsigned ofs)) in H3.
      2:{ apply Ptrofs.unsigned_range_2. }
      rewrite Int64.unsigned_repr_eq in H3.
      rewrite Z.sub_0_l in H3.
      destruct (dec (Ptrofs.unsigned ofs) 0).
      { unfold Ptrofs.to_int64 in H0. rewrite e in H0.
        unfold Ptrofs.sub in H0. change (Ptrofs.unsigned (Ptrofs.of_int64 _)) with 0 in H0.
        apply (f_equal Ptrofs.unsigned) in H0.
        rewrite Ptrofs.unsigned_repr_eq in H0.
        destruct (dec (Ptrofs.unsigned a) 0); et.
        rewrite Z_mod_nz_opp_full in H0. 
        2:{ rewrite Z.mod_small; et. apply Ptrofs.unsigned_range. }
        rewrite Z.mod_small in H0; et. 2:{ apply Ptrofs.unsigned_range. }
        change (Ptrofs.unsigned Ptrofs.zero) with 0 in H0. destruct a; ss. nia. }
      rewrite Z_mod_nz_opp_full in H3. 
      2:{ rewrite Z.mod_small; et; apply Ptrofs.unsigned_range. }
      rewrite Z.mod_small in H3. 2:{ apply Ptrofs.unsigned_range. }
      unfold Ptrofs.to_int64, Ptrofs.of_int64, Ptrofs.sub, Int64.sub in H0.
      rewrite (Int64.unsigned_repr (Ptrofs.unsigned _)) in H0.
      2:{ apply Ptrofs.unsigned_range_2. }
      change (Int64.unsigned Int64.zero) with 0 in H0.
      rewrite Z.sub_0_l in H0.
      rewrite Int64.unsigned_repr_eq in H0.
      rewrite Z_mod_nz_opp_full in H0. 2:{ rewrite Z.mod_small; et. apply Ptrofs.unsigned_range. }
      rewrite Z.mod_small in H0. 2:{ apply Ptrofs.unsigned_range. }
      rewrite Ptrofs.unsigned_repr_eq in H0.
      rewrite Z.mod_small in H0.
      2:{ destruct ofs. ss. change Int64.modulus with Ptrofs.modulus. nia. }
      destruct a; ss.
      apply (f_equal Ptrofs.unsigned) in H0.
      change (Ptrofs.unsigned Ptrofs.zero) with 0 in H0.
      rewrite Ptrofs.unsigned_repr in H0. 2:{ nia. }
      destruct ofs; ss. change Int64.modulus with (Ptrofs.max_unsigned + 1) in H0. nia.
    - iDestruct "A" as "%". des. destruct vaddr; ss; clarify.
  Qed.

  Lemma point_notundef
      p q m mvs :
    p (↦_m, q) mvs ⊢ ⌜p <> Vundef⌝.
  Proof.
    iIntros "A". unfold points_to.
    des_ifs. iDestruct "A" as "[_ A]". iDestruct "A" as (ofs) "[[_ A] _]".
    unfold _has_offset. des_ifs. iDestruct "A" as "[? ?]"; clarify.
  Qed.

  Lemma _offset_notundef
      p m tg q ofs :
    p (⊨_m,tg,q) ofs ⊢ ⌜p <> Vundef⌝.
  Proof.
    iIntros "A". unfold has_offset, _has_offset.
    des_ifs. iDestruct "A" as "[_ [_ []]]".
  Qed.

  Lemma live_notundef
      p m tg q :
    live_(m,tg,q) p ⊢ ⌜p <> Vundef⌝.
  Proof. apply _offset_notundef. Qed.

  Lemma live_notundef_ofs
      p m tg q ofs :
    live_(m,tg,q) (Val.subl p (Vptrofs ofs))⊢ ⌜p <> Vundef⌝.
  Proof. iIntros "A". iApply _offset_notundef. iApply live_offset_exchage. et. Qed.

  Lemma _offset_ptr
      {eff} {K:eventE -< eff} v m ofs :
    v ⊨m# ofs ⊢ ⌜@cast_to_ptr eff K v = Ret v⌝.
  Proof.
    iIntros "A". unfold has_offset.
    destruct v; ss; des_ifs_safe;
    iDestruct "A" as "[A %]"; clarify.
  Qed.

  Lemma _offset_cast_ptr
      {eff} {K:eventE -< eff} v m tg q ofs :
    v (⊨_m,tg,q) ofs ⊢ ⌜@cast_to_ptr eff K v = Ret v⌝.
  Proof.
    iIntros "A". unfold has_offset. des_ifs.
    unfold _has_offset.
    des_ifs; iDestruct "A" as "[_ [_ %]]"; clarify.
  Qed.

  Lemma live_cast_ptr
      {eff} {K:eventE -< eff} v m tg q :
    live_(m,tg,q) v ⊢ ⌜@cast_to_ptr eff K v = Ret v⌝.
  Proof. apply _offset_cast_ptr. Qed.

  Lemma live_cast_ptr_ofs
      {eff} {K:eventE -< eff} v m tg q ofs :
    live_(m,tg,q) (Val.subl v (Vptrofs ofs)) ⊢ ⌜@cast_to_ptr eff K v = Ret v⌝.
  Proof. iIntros "A". iApply _offset_cast_ptr. iApply live_offset_exchage. et. Qed.

  Lemma point_cast_ptr
      {eff} {K:eventE -< eff} v m q mvs :
    v (↦_m,q) mvs ⊢ ⌜@cast_to_ptr eff K v = Ret v⌝.
  Proof.
    iIntros "A". unfold points_to.
    destruct (blk m); clarify.
    iDestruct "A" as "[_ A]".
    iDestruct "A" as (ofs) "[[_ ?] _]".
    iApply _offset_ptr. et.
  Qed.

  Lemma ptrofs_cast_ptr
      {eff} {K:eventE -< eff} i :
    @cast_to_ptr eff K (Vptrofs i) = Ret (Vptrofs i).
  Proof. unfold cast_to_ptr. des_ifs. Qed.

  Lemma points_to_is_ptr
      v m q mvs :
    v (↦_m,q) mvs ⊢ ⌜is_ptr_val v = true⌝.
  Proof.
    iIntros "A". unfold points_to, _has_offset.
    destruct blk; clarify.
    iDestruct "A" as "[_ A]".
    iDestruct "A" as (ofs) "[[_ [_ A]] _]".
    des_ifs.
  Qed.

  Lemma _decode_encode_ptr_ofs
      v m tg q ofs :
    v (⊨_m,tg,q) ofs ⊢ ⌜decode_val Mptr (encode_val Mptr v) = v⌝.
  Proof.
    unfold Mptr. des_ifs.
    pose proof (decode_encode_val_general v Mint64 Mint64).
    unfold decode_encode_val in H0.
    iIntros "A". unfold has_offset, _has_offset.
    destruct v; try solve [iDestruct "A" as "[A [A' %]]"; clarify];
      des_ifs; rewrite H0; et.
    all: iDestruct "A" as "[_ [_ %]]"; clarify.
  Qed.

  Lemma decode_encode_ptr_live
      v m tg q :
    live_(m,tg,q) v ⊢ ⌜decode_val Mptr (encode_val Mptr v) = v⌝.
  Proof. apply _decode_encode_ptr_ofs. Qed.

  Lemma decode_encode_ptr_live_ofs
      v m tg q ofs :
    live_(m,tg,q) (Val.subl v (Vptrofs ofs)) ⊢ ⌜decode_val Mptr (encode_val Mptr v) = v⌝.
  Proof. iIntros "A". iApply _decode_encode_ptr_ofs. iApply live_offset_exchage. et. Qed.

  Lemma decode_encode_ptr_equiv
      p m q :
    p (≃_m) q ⊢ ⌜decode_val Mptr (encode_val Mptr p) = p⌝.
  Proof.
    unfold Mptr. des_ifs.
    pose proof (decode_encode_val_general p Mint64 Mint64).
    unfold decode_encode_val in H0.
    iIntros "A". iDestruct "A" as (ofs) "[A _]".
    destruct p; try solve [iDestruct "A" as "[? []]"].
    - rewrite H0. et.
    - des_ifs.
  Qed.

  Lemma _add_null_r
      v m tg q ofs:
    v (⊨_m,tg,q) ofs ⊢ ⌜Val.addl v (Vptrofs Ptrofs.zero) = v⌝.
  Proof.
    iIntros "A". unfold has_offset, _has_offset.
    des_ifs; try solve [iDestruct "A" as "[A [A' %]]"; clarify].
    - iPureIntro. ss. unfold Vptrofs. des_ifs.
      change (Ptrofs.to_int64 _) with Int64.zero.
      rewrite Int64.add_zero. et.
    - iPureIntro. ss. unfold Vptrofs. des_ifs.
      rewrite Ptrofs.of_int64_to_int64; et.
      rewrite Ptrofs.add_zero. et.
  Qed.

  Lemma add_null_r
      v m tg q :
    live_(m,tg,q) v ⊢ ⌜Val.addl v (Vptrofs Ptrofs.zero) = v⌝.
  Proof. apply _add_null_r. Qed.

  Lemma add_null_r_ofs
      v m tg q ofs:
    live_(m,tg,q) (Val.subl v (Vptrofs ofs)) ⊢ ⌜Val.addl v (Vptrofs Ptrofs.zero) = v⌝.
  Proof. iIntros "A". iApply _add_null_r. iApply live_offset_exchage. et. Qed.

  Lemma _sub_null_r
      v m tg q ofs:
    v (⊨_m,tg,q) ofs ⊢ ⌜Val.subl v (Vptrofs Ptrofs.zero) = v⌝.
  Proof.
    iIntros "A". unfold has_offset, _has_offset.
    des_ifs; try solve [iDestruct "A" as "[A [A' %]]"; clarify].
    - iPureIntro. ss. unfold Vptrofs. des_ifs.
      change (Ptrofs.to_int64 _) with Int64.zero.
      rewrite Int64.sub_zero_l. et.
    - iPureIntro. ss. unfold Vptrofs. des_ifs.
      rewrite Ptrofs.of_int64_to_int64; et.
      rewrite Ptrofs.sub_zero_l. et.
  Qed.

  Lemma sub_null_r
      v m tg q :
    live_(m,tg,q) v ⊢ ⌜Val.subl v (Vptrofs Ptrofs.zero) = v⌝.
  Proof. apply _sub_null_r. Qed.

End RULES.

Section SPEC.

  Context `{@GRA.inG Mem.t Σ}.

  (* input: Z, output: block *)
  Definition salloc_spec: fspec :=
    (mk_simple (fun n => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = n↑ /\ 0 < n ≤ Ptrofs.max_unsigned⌝),
                    (fun vret => ∃ m vaddr b,
                                 ⌜vret = b↑ /\ m.(blk) = Some b /\ m.(sz) = n ⌝
                                 ** vaddr (↦_m,1) List.repeat Undef (Z.to_nat n)
                                 ** live_(m, Local, 1) vaddr)
    )))%I.

  (* input: option block * Z, output: unit *)
  Definition sfree_spec: fspec :=
    (mk_simple (fun '() => (
                  (ord_pure 0%nat),
                  (fun varg => ∃ m mvs vaddr,
                                ⌜varg = (m.(blk), m.(sz))↑
                                /\ Z.of_nat (List.length mvs) = m.(sz)⌝
                                ** vaddr (↦_m,1) mvs
                                ** live_(m,Local,1) vaddr),
                  (fun vret => ⌜vret = tt↑⌝)
    )))%I.

  (* input: chunk * val, output: val *)
  Definition load_spec: fspec :=
    (mk_simple (fun '(chunk, vaddr, m, q, mvs) => (
                    (ord_pure 0%nat),
                    (fun varg => ∃ ofs, ⌜varg = (chunk, vaddr)↑
                                 /\ List.length mvs = size_chunk_nat chunk
                                 /\ Mem.change_check chunk mvs = false
                                 /\ chunk <> Many64
                                 /\ ((size_chunk chunk) | Ptrofs.unsigned ofs)⌝
                                 ** vaddr ⊨ m # ofs
                                 ** vaddr (↦_m,q) mvs),
                    (fun vret => ∃ v, ⌜vret = v↑ /\ decode_val chunk mvs = v⌝
                                 ** vaddr (↦_m,q) mvs)
    )))%I.

  (* input: chunk * val * val, output: unit *)
  Definition store_spec: fspec :=
    (mk_simple
      (fun '(chunk, vaddr, m, v_new) => (
            (ord_pure 0%nat),
            (fun varg => ∃ mvs_old ofs, ⌜varg = (chunk, vaddr, v_new)↑
                         /\ List.length mvs_old = size_chunk_nat chunk
                         /\ ((size_chunk chunk) | Ptrofs.unsigned ofs)⌝
                         ** vaddr ⊨ m # ofs
                         ** vaddr (↦_m,1) mvs_old),
            (fun vret => ∃ mvs_new, ⌜vret = tt↑
                         /\ encode_val chunk v_new = mvs_new⌝
                         ** vaddr (↦_m,1) mvs_new)
    )))%I.

  (* group of cmp_ptr rules *)
  (* input: comparison * val * val, output: bool *)

  Definition cmp_ofs (c: comparison) (ofs0 ofs1: Z) :=
    match c with
    | Ceq => ofs0 =? ofs1
    | Cne => negb (ofs0 =? ofs1)
    | Clt => ofs0 <? ofs1
    | Cle => ofs0 <=? ofs1
    | Cgt => ofs0 >? ofs1
    | Cge => ofs0 >=? ofs1
    end.

  Definition cmp_ptr_hoare0 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(c) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (c, Vnullptr, Vnullptr)↑⌝),
            (fun vret => ⌜vret = match c with
                                 | Ceq | Cle | Cge => true↑
                                 | _ => false↑
                                 end⌝)
          )%I.

  Definition cmp_ptr_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, tg, q, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Ceq, Vnullptr, vaddr)↑ /\ weak_valid m ofs⌝
                         ** live_(m,tg,q) (Val.subl vaddr (Vptrofs ofs))),
            (fun vret => ⌜vret = false↑⌝
                         ** live_(m,tg,q) (Val.subl vaddr (Vptrofs ofs)))
          )%I.

  Definition cmp_ptr_hoare2 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, tg, q, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Cne, Vnullptr, vaddr)↑ /\ weak_valid m ofs⌝
                         ** live_(m,tg,q) (Val.subl vaddr (Vptrofs ofs))),
            (fun vret => ⌜vret = true↑⌝
                         ** live_(m,tg,q) (Val.subl vaddr (Vptrofs ofs)))
          )%I.

  Definition cmp_ptr_hoare3 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, tg, q, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Ceq, vaddr, Vnullptr)↑ /\ weak_valid m ofs⌝
                         ** live_(m,tg,q) (Val.subl vaddr (Vptrofs ofs))),
            (fun vret => ⌜vret = false↑⌝
                         ** live_(m,tg,q) (Val.subl vaddr (Vptrofs ofs)))
          )%I.

  Definition cmp_ptr_hoare4 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, tg, q, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Cne, vaddr, Vnullptr)↑ /\ weak_valid m ofs⌝
                         ** live_(m,tg,q) (Val.subl vaddr (Vptrofs ofs))),
            (fun vret => ⌜vret = true↑⌝
                         ** live_(m,tg,q) (Val.subl vaddr (Vptrofs ofs)))
          )%I.

  Definition cmp_ptr_hoare5 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(c, vaddr0, vaddr1, m, ofs0, ofs1, q0, q1, tg) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (c, vaddr0, vaddr1)↑ /\ weak_valid m ofs0 /\ weak_valid m ofs1⌝
                         ** live_(m,tg,q0) (Val.subl vaddr0 (Vptrofs ofs0))
                         ** live_(m,tg,q1) (Val.subl vaddr1 (Vptrofs ofs1))),
            (fun vret => ⌜vret = (cmp_ofs c (Ptrofs.unsigned ofs0) (Ptrofs.unsigned ofs1))↑⌝
                         ** live_(m,tg,q0) (Val.subl vaddr0 (Vptrofs ofs0))
                         ** live_(m,tg,q1) (Val.subl vaddr1 (Vptrofs ofs1)))
          )%I.

  Definition cmp_ptr_hoare6 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr0, vaddr1, m0, m1, ofs0, ofs1, q0, q1, tg0, tg1) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Ceq, vaddr0, vaddr1)↑ /\ m0 #^ m1
                         /\ valid m0 ofs0 /\ valid m1 ofs1⌝
                         ** live_(m0,tg0,q0) (Val.subl vaddr0 (Vptrofs ofs0))
                         ** live_(m1,tg1,q1) (Val.subl vaddr1 (Vptrofs ofs1))),
            (fun vret => ⌜vret = false↑⌝
                         ** live_(m0,tg0,q0) (Val.subl vaddr0 (Vptrofs ofs0))
                         ** live_(m1,tg1,q1) (Val.subl vaddr1 (Vptrofs ofs1)))
          )%I.

  Definition cmp_ptr_hoare7 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr0, vaddr1, m0, m1, ofs0, ofs1, q0, q1, tg0, tg1) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (Cne, vaddr0, vaddr1)↑ /\ m0 #^ m1
                         /\ valid m0 ofs0 /\ valid m1 ofs1⌝
                         ** live_(m0,tg0,q0) (Val.subl vaddr0 (Vptrofs ofs0))
                         ** live_(m1,tg1,q1) (Val.subl vaddr1 (Vptrofs ofs1))),
            (fun vret => ⌜vret = true↑⌝
                         ** live_(m0,tg0,q0) (Val.subl vaddr0 (Vptrofs ofs0))
                         ** live_(m1,tg1,q1) (Val.subl vaddr1 (Vptrofs ofs1)))
          )%I.

  Definition cmp_ptr_spec: fspec :=
    mk_simple (
      cmp_ptr_hoare0
      @ cmp_ptr_hoare1
      @ cmp_ptr_hoare2
      @ cmp_ptr_hoare3
      @ cmp_ptr_hoare4
      @ cmp_ptr_hoare5
      @ cmp_ptr_hoare6
      @ cmp_ptr_hoare7
    ).

  (* input: Z * val * val, output: val *)
  Definition sub_ptr_spec : fspec :=
    (mk_simple
      (fun '(size, vaddr0, vaddr1, m, ofs0, ofs1, q0, q1, tg) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = (size, vaddr0, vaddr1)↑ /\ 0 < size ≤ Ptrofs.max_signed
                         /\ Ptrofs.min_signed ≤ Ptrofs.unsigned ofs0 - Ptrofs.unsigned ofs1 ≤ Ptrofs.max_signed
                         /\ weak_valid m ofs0 /\ weak_valid m ofs1⌝
                         ** live_(m,tg,q0) (Val.subl vaddr0 (Vptrofs ofs0))
                         ** live_(m,tg,q1) (Val.subl vaddr1 (Vptrofs ofs1))),
            (fun vret => ⌜vret = (Vptrofs (Ptrofs.repr (Z.quot (Ptrofs.unsigned ofs0 - Ptrofs.unsigned ofs1) size)))↑⌝
                         ** live_(m,tg,q0) (Val.subl vaddr0 (Vptrofs ofs0))
                         ** live_(m,tg,q1) (Val.subl vaddr1 (Vptrofs ofs1)))
    )))%I.

  (* input: val, output: bool *)
  Definition non_null_spec: fspec :=
    (mk_simple
      (fun '(vaddr, m, q, tg, ofs) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = vaddr↑ /\ weak_valid m ofs⌝
                         ** live_(m,tg,q) (Val.subl vaddr (Vptrofs ofs))),
            (fun vret => ⌜vret = true↑⌝
                         ** live_(m,tg,q) (Val.subl vaddr (Vptrofs ofs)))
    )))%I.

  (* builtin-like functions of clight *)
  (* input: list val, output: val *)

  (* heap malloc free *)
  Definition malloc_spec: fspec :=
    (mk_simple (fun n => (
                    (ord_pure 0%nat),
                    (fun varg => ⌜varg = [Vptrofs n]↑ /\ Ptrofs.unsigned n > 0⌝),
                    (fun vret => ∃ m vaddr, ⌜vret = vaddr↑ /\ m.(sz) = Ptrofs.unsigned n⌝
                                 ** vaddr (↦_m,1) List.repeat Undef (Z.to_nat (Ptrofs.unsigned n))
                                 ** live_(m,Dynamic,1) vaddr)
    )))%I.

  Definition mfree_spec: fspec :=
    (mk_simple (fun '() => (
                    (ord_pure 0%nat),
                    (fun varg => ∃ m mvs vaddr,
                                 ⌜varg = [vaddr]↑ /\ Z.of_nat (List.length mvs) = m.(sz)⌝
                                 ** vaddr (↦_m,1) mvs
                                 ** live_(m,Dynamic,1) vaddr),
                    (fun vret => ⌜vret = Vundef↑⌝)
    )))%I.

  (* memcpy *)
  Definition memcpy_hoare0 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, vaddr', qp, m_src, m_dst, mvs_src) => (
            (ord_pure 0%nat),
            (fun varg => ∃ al sz mvs_dst ofs_src ofs_dst,
                         ⌜varg = (al, sz, [vaddr; vaddr'])↑
                         /\ List.length mvs_src = List.length mvs_dst
                         /\ List.length mvs_dst = Z.to_nat sz
                         /\ (al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
                         /\ (al | Ptrofs.unsigned ofs_src)
                         /\ (al | Ptrofs.unsigned ofs_dst)
                         /\ 0 ≤ sz /\ (al | sz)⌝
                         ** vaddr' ⊨ m_src # ofs_src
                         ** vaddr ⊨ m_dst # ofs_dst
                         ** vaddr' (↦_m_src,qp) mvs_src
                         ** vaddr (↦_m_dst,1) mvs_dst),
            (fun vret => ⌜vret = Vundef↑⌝
                         ** vaddr' (↦_m_src,qp) mvs_src
                         ** vaddr (↦_m_dst,1) mvs_src)
          )%I.

  Definition memcpy_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m_dst, mvs_dst) => (
            (ord_pure 0%nat),
            (fun varg => ∃ al sz ofs_dst,
                         ⌜varg = (al, sz, [vaddr; vaddr])↑
                         /\ List.length mvs_dst = Z.to_nat sz
                         /\ (al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
                         /\ (al | Ptrofs.unsigned ofs_dst)
                         /\ 0 ≤ sz /\ (al | sz)⌝
                         ** vaddr ⊨ m_dst # ofs_dst
                         ** vaddr (↦_m_dst,1) mvs_dst),
            (fun vret => ⌜vret = Vundef↑⌝
                         ** vaddr (↦_m_dst,1) mvs_dst)
          )%I.

  Definition memcpy_spec: fspec :=
    mk_simple (memcpy_hoare0 @ memcpy_hoare1).

  (* capture *)
  Definition capture_hoare0 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '() => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = [Vnullptr]↑⌝),
            (fun vret => ⌜vret = (Vnullptr)↑⌝ )
          )%I.

  Definition capture_hoare1 : _ -> ord * (Any.t -> iProp) * (Any.t -> iProp) :=
      fun '(vaddr, m, q, ofs, tg) => (
            (ord_pure 0%nat),
            (fun varg => ⌜varg = [vaddr]↑⌝
                         ** live_(m,tg,q) (Val.subl vaddr (Vptrofs ofs))),
            (fun vret => ∃ i, ⌜vret = (Vptrofs i)↑⌝
                         ** live_(m,tg,q) (Val.subl vaddr (Vptrofs ofs))
                         ** vaddr (≃_m) (Vptrofs i))
          )%I.

  Definition capture_spec: fspec :=
    mk_simple (capture_hoare0 @ capture_hoare1).

  (* sealed *)
  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("salloc", salloc_spec); ("sfree", sfree_spec);
           ("load", load_spec);
           (* ("loadbytes", loadbytes_spec);  *)
           ("store", store_spec);
           (* ("storebytes", storebytes_spec); *)
           ("sub_ptr", sub_ptr_spec); ("cmp_ptr", cmp_ptr_spec);
           ("non_null?", non_null_spec);
           ("malloc", malloc_spec); ("free", mfree_spec);
           ("memcpy", memcpy_spec);
           ("capture", capture_spec)
           ].
    Defined.

End SPEC.

Section MRS.

  Context `{@GRA.inG Mem.t Σ}.

  Variable sk: Sk.t.
  Let skenv: SkEnv.t := load_skenv sk.

  Definition store_init_data (res : ClightPlusMemRA.__pointstoRA) (b : block) (p : Z) (optq : option Qp) (id : init_data) : option ClightPlusMemRA.__pointstoRA :=
    match id with
    | Init_int8 n =>
      if Zdivide_dec (align_chunk Mint8unsigned) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint8unsigned (Vint n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_int16 n =>
      if Zdivide_dec (align_chunk Mint16unsigned) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint16unsigned (Vint n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_int32 n =>
      if Zdivide_dec (align_chunk Mint32) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint32 (Vint n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_int64 n =>
      if Zdivide_dec (align_chunk Mint64) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mint64 (Vlong n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_float32 n =>
      if Zdivide_dec (align_chunk Mfloat32) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mfloat32 (Vsingle n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_float64 n =>
      if Zdivide_dec (align_chunk Mfloat64) p
      then
        match optq with
        | Some q => Some (__points_to b p (encode_val Mfloat64 (Vfloat n)) q ⋅ res)
        | None => Some res
        end
      else None
    | Init_space z =>
      match optq with
      | Some q => Some (__points_to b p (repeat (Byte Byte.zero) (Z.to_nat z)) q ⋅ res)
      | None => Some res
      end
    | Init_addrof symb ofs =>
      match SkEnv.id2blk skenv (string_of_ident symb) with
      | Some b' =>
        if Zdivide_dec (align_chunk Mptr) p
        then
          match optq with
          | Some q => Some (__points_to b p (encode_val Mptr (Vptr (Pos.of_succ_nat b') ofs)) q ⋅ res)
          | None => Some res
          end
        else None
      | None => None
      end
    end.

  Fixpoint store_init_data_list (res : ClightPlusMemRA.__pointstoRA) (b : block) (p : Z) (optq: option Qp) (idl : list init_data) {struct idl} : option ClightPlusMemRA.__pointstoRA :=
    match idl with
    | [] => Some res
    | id :: idl' =>
        match store_init_data res b p optq id with
        | Some res' => store_init_data_list res' b (p + init_data_size id)%Z optq idl'
        | None => None
        end
    end.

  Definition alloc_global (res : ClightPlusMemRA.__pointstoRA * ClightPlusMemRA.__allocatedRA * ClightPlusMemRA._blocksizeRA) (b: block) (gd : globdef fundef type) : option (ClightPlusMemRA.__pointstoRA * ClightPlusMemRA.__allocatedRA * ClightPlusMemRA._blocksizeRA) :=
    let '(p, a, s) := res in
    match gd with
    | Gfun _ => Some (p, a ⋅ (__allocated_with b Unfreeable (1/2)%Qp), s ⋅ (__has_size (Some b) 1))
    | Gvar v =>
      let optq := match Globalenvs.Genv.perm_globvar v with
                  | Freeable | Writable => Some 1%Qp
                  | Readable => Some (1/2)%Qp
                  | Nonempty => None
                  end
      in
      match store_init_data_list ε b 0 optq (gvar_init v) with
      | Some res' => Some (p ⋅ res', a ⋅ (__allocated_with b Unfreeable (1/2)%Qp), s ⋅ (__has_size (Some b) (init_data_list_size (gvar_init v))))
      | None => None
      end
    end.

  Fixpoint alloc_globals (res : ClightPlusMemRA.__pointstoRA * ClightPlusMemRA.__allocatedRA * ClightPlusMemRA._blocksizeRA) (b: block) (sk: Sk.t) : option (ClightPlusMemRA.__pointstoRA * ClightPlusMemRA.__allocatedRA * ClightPlusMemRA._blocksizeRA) :=
    match sk with
    | nil => Some res
    | g :: gl' =>
      let (_, gd) := g in
      match alloc_global res b gd with
      | Some res' => alloc_globals res' (Pos.succ b) gl'
      | None => None
      end
    end.

  Definition res_init : Mem.t :=
    match alloc_globals (ε, ε, ε) xH sk with
    | Some (p, a, s) => (Auth.black p, Auth.black a,
                          s ⋅ (fun ob =>
                                match ob with
                                | Some b => if Coqlib.plt b (Pos.of_succ_nat (List.length sk)) then OneShot.unit else OneShot.black
                                | None => OneShot.white 0
                                end) : ClightPlusMemRA._blocksizeRA,
                          fun ob =>
                            match ob with
                            | Some _ => OneShot.black
                            | None => OneShot.white Ptrofs.zero
                            end)
    | None => (Auth.black ε, Auth.black ε,
                fun ob =>
                  match ob with
                  | Some _ => OneShot.black
                  | None => OneShot.white 0
                  end,
                fun ob =>
                  match ob with
                  | Some _ => OneShot.black
                  | None => OneShot.white Ptrofs.zero
                  end)
    end.

End MRS.

Section SMOD.

  Context `{@GRA.inG Mem.t Σ}.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("salloc", mk_pure salloc_spec);
    ("sfree",   mk_pure sfree_spec);
    ("load",   mk_pure load_spec);
    (* ("loadbytes",   mk_pure loadbytes_spec); *)
    ("store",  mk_pure store_spec);
    (* ("storebytes",   mk_pure storebytes_spec); *)
    ("sub_ptr", mk_pure sub_ptr_spec);
    ("cmp_ptr", mk_pure cmp_ptr_spec);
    ("non_null?",   mk_pure non_null_spec);
    ("malloc",   mk_pure malloc_spec);
    ("free",   mk_pure mfree_spec);
    ("memcpy", mk_pure memcpy_spec);
    ("capture", mk_pure capture_spec)
    ]
  .

  Definition SMemSem sk : SModSem.t :=
    {|
      SModSem.fnsems := MemSbtb;
      SModSem.mn := "Mem";
      SModSem.initial_mr := GRA.embed (res_init sk);
      SModSem.initial_st := tt↑;
    |} .

  Definition SMem sk: SMod.t := {|
    SMod.get_modsem := SMemSem;
    SMod.sk := sk;
  |}
  .

  Definition Mem sk: Mod.t := (SMod.to_tgt (fun _ => to_stb [])) (SMem sk).

End SMOD.

Global Hint Unfold MemStb: stb.

Global Opaque _points_to.
Global Opaque _allocated_with.
Global Opaque _has_size.
Global Opaque _has_base.
Global Opaque equiv_prov.
