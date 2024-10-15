Require Import CoqlibCCR.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import Any.
Require Import ModSem.
Require Import ModSemE.
Require Import ClightPlusMemRA.
Require Import ClightPlusMem1.
From compcert Require Export Ctypes Values AST Memdata Integers.

Set Implicit Arguments.

Section PROP.

  Context `{@GRA.inG Mem.t Σ}.

  Definition vlist_delete_hd (l: list val) (default: val) : val * list val := (hd default l, tl l).

  Definition vlist_delete_tl (l: list val) (default: val) : val * list val := (last l default, removelast l).

  Definition check_inbound (l: list val) (from_tail: val) (index: val) : option nat :=
    match index with
    | Vint i =>
      if negb (Coqlib.zle 0 (Int.unsigned i) && Coqlib.zlt (Int.unsigned i) (Z.of_nat (List.length l)))
      then None
      else if Val.eq Vzero from_tail then Some (Z.to_nat (Int.unsigned i))
           else Some (List.length l - Z.to_nat (Int.unsigned i))
    | Vlong i =>
      if negb (Coqlib.zle 0 (Int64.unsigned i) && Coqlib.zlt (Int64.unsigned i) (Z.of_nat (List.length l)))
      then None
      else if Val.eq Vzero from_tail then Some (Z.to_nat (Int64.unsigned i))
           else Some (List.length l - Z.to_nat (Int64.unsigned i))
    | _ => None
    end.

     (* is_xorlist represents the figure below    *)
     (*    ll_h                              ll_t *)
     (*     |                                 |   *)
     (*     v                                 v   *)
     (* xs  - - - - - - - - - - - - - - - - - -   *)

  Fixpoint frag_xorlist (q: Qp) (m_prev m_next: metadata) (hd_prev hd tl tl_next: val) (xs : list val) {struct xs} : iProp :=
    match xs with
    | [] => (hd_prev (≃_ m_prev) tl ** hd (≃_ m_next) tl_next)
    | Vlong a :: xs' =>
        ∃ i_prev i_next m_hd,
          ⌜m_hd.(sz) = (size_chunk Mint64 + size_chunk Mptr)%Z⌝
          ** hd_prev (≃_ m_prev) (Vptrofs i_prev)
          ** live_(m_hd,Dynamic,q) hd
          ** hd (↦_m_hd,q) (encode_val Mint64 (Vlong a) ++ encode_val Mptr (Vptrofs (Ptrofs.xor i_prev i_next)))
          ** frag_xorlist q m_hd m_next hd (Vptrofs i_next) tl tl_next xs'
    | _ => False
    end%I.

  Lemma unfold_frag_xorlist (q: Qp) (m_prev m_next: metadata) (hd_prev hd tl tl_next: val) (xs : list val) :
  frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs =
    match xs with
    | [] => (hd_prev (≃_ m_prev) tl ** hd (≃_ m_next) tl_next)
    | Vlong a :: xs' =>
        ∃ i_prev i_next m_hd,
          ⌜m_hd.(sz) = (size_chunk Mint64 + size_chunk Mptr)%Z⌝
          ** hd_prev (≃_ m_prev) (Vptrofs i_prev)
          ** live_(m_hd,Dynamic,q) hd
          ** hd (↦_m_hd,q) (encode_val Mint64 (Vlong a) ++ encode_val Mptr (Vptrofs (Ptrofs.xor i_prev i_next)))
          ** frag_xorlist q m_hd m_next hd (Vptrofs i_next) tl tl_next xs'
    | _ => False
    end%I.
  Proof. des_ifs. Qed.


  Definition full_xorlist q hd_hdl tl_hdl xs : iProp :=
    (∃ m_hd_hdl m_tl_hdl hd tl ofs_hd_hdl ofs_tl_hdl,
    hd_hdl (↦_m_hd_hdl,q) (encode_val Mptr hd)
    ** hd_hdl ⊨ m_hd_hdl # ofs_hd_hdl
    ** ⌜m_hd_hdl.(sz) = size_chunk Mptr /\ ((size_chunk Mptr) | Ptrofs.unsigned ofs_hd_hdl)%Z⌝
    ** tl_hdl (↦_m_tl_hdl,q) (encode_val Mptr tl)
    ** tl_hdl ⊨ m_tl_hdl # ofs_tl_hdl
    ** ⌜m_tl_hdl.(sz) = size_chunk Mptr /\ ((size_chunk Mptr) | Ptrofs.unsigned ofs_tl_hdl)%Z⌝
    ** frag_xorlist q m_null m_null Vnullptr hd tl Vnullptr xs)%I.

  Lemma rev_xorlist q m_prev m_next hd_prev hd tl tl_next xs
    : frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs
      ⊢ frag_xorlist q m_next m_prev tl_next tl hd hd_prev (rev xs).
  Proof.
    ginduction xs; i; ss.
    - iIntros "[A B]".
      iPoseProof (equiv_sym with "A") as "A".
      iPoseProof (equiv_sym with "B") as "B". iFrame.
    - destruct a; try solve [iIntros "[]"].
      iIntros "A".
      iDestruct "A" as (i_prev i_next m_hd) "[[[[% D] C] B] A]".
      iPoseProof (IHxs with "A") as "A".
      generalize (rev xs). i.
      iStopProof. clear - H0. ginduction l; i; ss.
      + iIntros "[A [B [C [D E]]]]".
        iPoseProof (equiv_sym with "E") as "E".
        iPoseProof (equiv_dup with "E") as "[E E']".
        iCombine "E' B" as "B".
        iPoseProof (equiv_live_comm with "B") as "B".
        iPoseProof (equiv_dup with "E") as "[E E']".
        iCombine "E' C" as "C".
        iPoseProof (equiv_point_comm with "C") as "C".
        iPoseProof (equiv_sym with "A") as "A".
        iPoseProof (equiv_sym with "E") as "E".
        rewrite Ptrofs.xor_commut.
        iExists i_next,i_prev,_. iFrame.
        et.
      + iIntros "[A [B [C D]]]".
        destruct a; try solve [iDestruct "D" as "[]"].
        iDestruct "D" as (i_prev0 i_next0 m_hd0) "[[[[% G] D] E] F]".
        iExists _,_,_. iFrame. iSplit; ss.
        iApply IHl. { apply H0. } iFrame.
  Qed.

  Lemma xorlist_hd_deen q m_prev m_next hd_prev hd tl tl_next xs
    : frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs ⊢ ⌜decode_val Mptr (encode_val Mptr hd) = hd⌝.
  Proof.
    destruct xs.
    - ss. iIntros "[A B]". iApply decode_encode_ptr_equiv. et.
    - ss. iIntros "A". destruct v; clarify.
      iDestruct "A" as (i_prev i_next m_hd) "[[[_ A] _] _]".
      iApply decode_encode_ptr_live. et.
  Qed.

  Lemma xorlist_hd_not_Vundef q m_prev m_next hd_prev hd tl tl_next xs
    : frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs ⊢ ⌜hd <> Vundef⌝.
  Proof.
    destruct xs.
    - ss. iIntros "[A B]". iApply equiv_notundef. et.
    - ss. des_ifs; et. iIntros "A".
      iDestruct "A" as (i_prev i_next m_hd) "[[[_ A] _] _]".
      iApply live_notundef. et.
  Qed.

  Lemma xorlist_tl_deen q m_prev m_next hd_prev hd tl tl_next xs
    : frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs ⊢ ⌜decode_val Mptr (encode_val Mptr tl) = tl⌝.
  Proof.
    iIntros "A". iInduction xs as [|item xs'] "IH" forall (m_prev m_next hd_prev hd tl tl_next); ss.
    - iApply decode_encode_ptr_equiv. iApply equiv_sym. iDestruct "A" as "[$ _]".
    - destruct item; clarify.
      iDestruct "A" as (i_prev i_next m_hd) "[_ A]".
      iApply "IH". et.
  Qed.

  Lemma xorlist_tl_not_Vundef q m_prev m_next hd_prev hd tl tl_next xs
    : frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs ⊢ ⌜tl <> Vundef⌝.
  Proof.
    ginduction xs; i; ss.
    - ss. iIntros "[A B]". iApply equiv_notundef. iApply equiv_sym. et.
    - ss. iIntros "A". destruct a; clarify.
      iDestruct "A" as (i_prev i_next m_hd) "[_ A]".
      iApply IHxs. et.
  Qed.

  Lemma xorlist_hd_prev_replace q m_prev m_next hd_prev hd_prev' hd tl tl_next xs
    : frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs ** hd_prev (≃_m_prev) hd_prev' ⊢ frag_xorlist q m_prev m_next hd_prev' hd tl tl_next xs.
  Proof.
    destruct xs; i; ss.
    - ss. iIntros "[[A B] C]". iFrame. iApply equiv_trans. iFrame. iApply equiv_sym. et.
    - ss. iIntros "[A B]". destruct v; clarify.
      iDestruct "A" as (i_prev i_next m_hd) "[[[[% F] D] E] A]".
      iExists _,_,_. iFrame. iSplit; ss. iApply equiv_trans. iFrame. iApply equiv_sym. et.
  Qed.

  Lemma xorlist_tl_next_replace q m_prev m_next hd_prev tl_next' hd tl tl_next xs
    : frag_xorlist q m_prev m_next hd_prev hd tl tl_next xs ** tl_next (≃_m_next) tl_next' ⊢ frag_xorlist q m_prev m_next hd_prev hd tl tl_next' xs.
  Proof.
    iIntros "[A B]". set xs at 1. rewrite <- (rev_involutive xs). unfold l.
    iApply rev_xorlist. iApply xorlist_hd_prev_replace. iFrame.
    iApply rev_xorlist. et.
  Qed.

End PROP.

Section SPEC.

  Context `{@GRA.inG Mem.t Σ}.

  Definition add_hd_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, item, xs) => (
        (ord_pure 1%nat),
        (fun varg => ⌜varg = [hd_handler; tl_handler; Vlong item]↑⌝
                     ** full_xorlist 1 hd_handler tl_handler xs),
        (fun vret => ⌜vret = Vundef↑⌝
                     ** full_xorlist 1 hd_handler tl_handler (Vlong item :: xs))
    )))%I.

  Definition add_tl_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, item, xs) => (
        (ord_pure 1%nat),
        (fun varg => ⌜varg = [hd_handler; tl_handler; Vlong item]↑⌝
                     ** full_xorlist 1 hd_handler tl_handler xs),
        (fun vret => ⌜vret = Vundef↑⌝
                     ** full_xorlist 1 hd_handler tl_handler (xs ++ [Vlong item]))
    )))%I.

  Definition delete_hd_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, xs) => (
        (ord_pure 1%nat),
        (fun varg => ⌜varg = [hd_handler; tl_handler]↑⌝
                     ** full_xorlist 1 hd_handler tl_handler xs),
        (fun vret => let '(item, xs') := vlist_delete_hd xs (Vlong Int64.zero) in
                     ⌜vret = item↑⌝ ** full_xorlist 1 hd_handler tl_handler xs')
    )))%I.

  Definition delete_tl_spec : fspec :=
    (mk_simple
      (fun '(hd_handler, tl_handler, xs) => (
        (ord_pure 1%nat),
        (fun varg => ⌜varg = [hd_handler; tl_handler]↑⌝
                     ** full_xorlist 1 hd_handler tl_handler xs),
        (fun vret => let '(item, xs') := vlist_delete_tl xs (Vlong Int64.zero) in
                     ⌜vret = item↑⌝ ** full_xorlist 1 hd_handler tl_handler xs')
    )))%I.

  (* sealed *)
  Definition xorStb : list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [
           ("add_hd", add_hd_spec);
           ("add_tl", add_tl_spec);
           ("delete_hd", delete_hd_spec);
           ("delete_tl", delete_tl_spec)
           (* ("search", search_spec) *)
           ].
  Defined.

End SPEC.

Section SMOD.

  Context `{@GRA.inG Mem.t Σ}.

  Definition xorSbtb: list (gname * fspecbody) :=
    [
     ("add_hd", mk_pure add_hd_spec);
     ("add_tl", mk_pure add_tl_spec);
     ("delete_hd", mk_pure delete_hd_spec);
     ("delete_tl", mk_pure delete_tl_spec)
     ].

End SMOD.
