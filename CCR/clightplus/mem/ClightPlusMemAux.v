Require Import CoqlibCCR.
From compcert Require Import AST Integers Values Memory Globalenvs.
From stdpp Require Import numbers.

Local Open Scope Z.

Lemma repeat_nth_some
  X (x: X) n ofs
  (IN: (ofs < n)%nat):
  <<NTH: nth_error (repeat x n) ofs = Some x>>.
Proof.
  ginduction n; ii; ss.
  - lia.
  - destruct ofs; ss. exploit IHn; et. lia.
Qed.

Lemma repeat_nth_none
  X (x: X) sz ofs
  (IN: ~(ofs < sz)%nat) :
  <<NTH: nth_error (repeat x sz) ofs = None>>.
Proof.
  generalize dependent ofs. induction sz; ii; ss.
  - destruct ofs; ss.
  - destruct ofs; ss. { lia. } hexploit (IHsz ofs); et. lia.
Qed.

Lemma repeat_nth
  X (x: X) sz ofs :
  nth_error (repeat x sz) ofs = if (ofs <? sz)%nat then Some x else None
.
Proof.
  des_ifs.
  - eapply repeat_nth_some; et. rewrite <- Nat.ltb_lt. et.
  - eapply repeat_nth_none; et. rewrite Nat.ltb_ge in Heq. lia.
Qed.

Local Transparent Mem.alloc.
Local Transparent Mem.store.

Local Ltac solve_len := unfold encode_int, bytes_of_int, rev_if_be, inj_bytes in *;
                        change Archi.big_endian with false in *;
                        change Archi.ptr64 with true in *; ss.

Lemma nth_error_ext A (l0 l1: list A) : (forall i, nth_error l0 i = nth_error l1 i) -> l0 = l1.
Proof.
  revert l1. induction l0; i; ss.
  - specialize (H 0%nat). ss. destruct l1; ss.
  - dup H. specialize (H 0%nat). ss. destruct l1; ss. clarify. f_equal.
    apply IHl0. i. specialize (H0 (S i)). ss.
Qed.

Lemma nth_error_getN n i m idx :
  (idx < n)%nat ->
  nth_error (Mem.getN n i m) idx = Some (Maps.ZMap.get (i + (Z.of_nat idx)) m).
Proof.
  i. ginduction n; i; ss; try nia.
  destruct idx.
  - ss. rewrite Z.add_0_r. et.
  - ss. replace (i + S idx) with ((i + 1) + idx) by nia. apply IHn. nia.
Qed.

Lemma setN_inside x l i c entry
  (IN_RANGE: i ≤ x /\ (x < i + Z.of_nat (length l)))
  (ENTRY: nth_error l (Z.to_nat (x - i)) = Some entry)
:
  Maps.ZMap.get x (Mem.setN l i c) = entry.
Proof.
  assert (Z.to_nat (x - i)%Z < length l)%nat by nia.
  apply nth_error_Some in H. destruct (nth_error _ _) eqn: E in H; clarify.
  clear H. move l at top. revert_until l. induction l; i; ss; try nia.
  destruct (Nat.eq_dec (Z.to_nat (x - i)) 0).
  - rewrite e in *. ss. clarify. assert (x = i) by nia. rewrite H in *.
    rewrite Mem.setN_outside; try nia. apply Maps.ZMap.gss.
  - change (a :: l) with ([a] ++ l) in E. rewrite nth_error_app2 in E; ss; try nia.
    replace (Z.to_nat (x - i) - 1)%nat with (Z.to_nat (x - (i + 1))) in E by nia.
    eapply IHl; et. nia.
Qed.


Lemma alloc_store_zero_condition m m0 m1 start len b
  (ALLOC: Mem.alloc m start (start + len) = (m0, b))
  (STORE_ZEROS: Globalenvs.R_store_zeros m0 b start len (Some m1))
:
  <<FILLED_ZERO: forall ofs, start ≤ ofs < start + len ->
                  Maps.ZMap.get ofs (Maps.PMap.get b m1.(Mem.mem_contents)) = Byte Byte.zero>>.
Proof.
  unfold Mem.alloc in ALLOC. clarify.
  remember (Some m1) as optm in STORE_ZEROS.
  move STORE_ZEROS at top. revert_until STORE_ZEROS.
  induction STORE_ZEROS; red; i; ss; try nia.
  destruct (Coqlib.zlt ofs (p + 1)).
  - assert (Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m1)) =
              Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m'))).
    { set (p + 1) as p' in *. set (n - 1) as n' in *.
      clear -l STORE_ZEROS Heqoptm. clearbody p' n'. move STORE_ZEROS at top.
      revert_until STORE_ZEROS.
      induction STORE_ZEROS; i; ss; clarify; try nia.
      rewrite IHSTORE_ZEROS; et; try nia. unfold Mem.store in e0.
      des_ifs. ss. rewrite Maps.PMap.gss. rewrite Mem.setN_outside; et. }
    rewrite H0. unfold Mem.store in e0. des_ifs. ss.
    rewrite Maps.PMap.gss. erewrite setN_inside; solve_len; try nia.
    replace (ofs - p) with 0 by nia. et.
  - hexploit IHSTORE_ZEROS; et. i. des. eapply H0. nia.
Qed.

Lemma match_mem_getN f (c d: Maps.ZMap.t memval) n p
    (MM: forall i mv, Maps.ZMap.get i c = mv -> Maps.ZMap.get i d = f mv)
  :
    Mem.getN n p d = map f (Mem.getN n p c).
Proof.
  revert p. induction n; i; ss.
  rewrite IHn. f_equal. erewrite <- MM; try reflexivity.
Qed.

Lemma proj_determines_decode_val l :
  proj_bytes l = None -> proj_fragment l = None -> decode_val Mptr l = Vundef.
Proof.
  i. unfold decode_val. des_ifs.
  destruct l; ss. destruct m; et.
  destruct proj_fragment eqn: X; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  do 5 (destruct n; clarify).
  destruct n; clarify.
  destruct n; clarify.
  destruct n; clarify.
  ss. destruct l; clarify. destruct m; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  do 7 (destruct n; clarify). ss.
  destruct l; clarify. destruct m; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  do 6 (destruct n; clarify). ss.
  destruct l; clarify. destruct m; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  do 5 (destruct n; clarify). ss.
  destruct l; clarify. destruct m; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  do 4 (destruct n; clarify). ss.
  destruct l; clarify. destruct m; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  do 3 (destruct n; clarify). ss.
  destruct l; clarify. destruct m; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  do 2 (destruct n; clarify). ss.
  destruct l; clarify. destruct m; clarify.
  destruct Val.eq; ss. destruct quantity_eq; ss.
  destruct n; clarify. ss.
  destruct l; clarify.
Qed.

Lemma decode_val_undef mvl chunk : In Undef mvl -> decode_val chunk mvl = Vundef.
Proof.
  i. unfold decode_val. hexploit Mem.proj_bytes_undef; et. i. rewrite H0.
  des_ifs.
  - hexploit proj_value_undef; et. i. rewrite H1. ss.
  - hexploit proj_value_undef; et. i. rewrite H1. ss.
  - hexploit proj_value_undef; et.
Qed.

Lemma pure_memval_good_decode l chunk mem :
    Mem.change_check chunk l = false -> chunk <> Many64 ->
    decode_val chunk (Mem.normalize_mvs chunk mem l) = decode_val chunk l.
Proof.
  destruct chunk; clarify. i.
  (* normalize check *)
  unfold Mem.change_check in H. bsimpl. des.
  - unfold Mem.normalize_mvs. rewrite H. et.
  - f_equal. unfold Mem.normalize_mvs. des_ifs.
    revert H. clear Heq. induction l; ss. i. bsimpl. des. destruct a; ss.
    f_equal. et.
  - des_ifs.
    + unfold Mem.normalize_mvs. des_ifs; clear Heq.
      bsimpl. assert (In Undef l). { clear -H. induction l; ss. bsimpl. des; et. destruct a; ss; et. }
      hexploit decode_val_undef; et. i. rewrite H2.
      apply in_map with (f:=Mem._decode_normalize_mv mem) in H1.
      hexploit decode_val_undef; et.
    + unfold Mem.normalize_mvs. des_ifs; clear Heq0.
      unfold Mem.qarchi in Heq. des_ifs.
      unfold proj_value in Heq.
      des_ifs. ss.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      unfold rev_if_be_mv. destruct Archi.big_endian eqn:?; clarify.
      unfold inj_bytes. ss. unfold encode_int. ss. unfold rev_if_be. rewrite Heqb. ss.
      unfold decode_val. ss. des_ifs.
    + unfold Mem.normalize_mvs. des_ifs; clear Heq0.
      unfold Mem.qarchi in Heq. des_ifs.
      unfold proj_value in Heq.
      des_ifs. ss.
      Local Opaque nth_error encode_val. ss.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      unfold rev_if_be_mv. destruct Archi.big_endian eqn:?; clarify.
      set (_ :: _). replace l with (encode_val Mint64 (Vlong i)) by ss.
      pose proof (decode_encode_val_general (Vlong i) Mint64 Mint64).
      rewrite H1. unfold decode_val. ss.
      destruct Val.eq; clarify.
    + unfold Mem.normalize_mvs. des_ifs; clear Heq0.
      unfold Mem.qarchi in Heq. des_ifs.
      unfold proj_value in Heq.
      des_ifs. ss.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
    + unfold Mem.normalize_mvs. des_ifs; clear Heq0.
      unfold Mem.qarchi in Heq. des_ifs.
      unfold proj_value in Heq.
      des_ifs. ss.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
    + unfold Mem.qarchi in Heq. des_ifs.
      unfold proj_value in Heq.
      des_ifs. ss.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
      destruct m; clarify.
      destruct Val.eq; clarify. ss.
      destruct quantity_eq; clarify. ss.
      destruct n; clarify. bsimpl.
      destruct l0; clarify.
  Qed.

Lemma concrete_store_zeros m1 b p n m2
        (STORE: store_zeros m1 b p n = Some m2):
  m1.(Mem.mem_concrete)= m2.(Mem.mem_concrete).
Proof.
  simpl in STORE. symmetry in STORE. apply Globalenvs.R_store_zeros_correct in STORE.
  remember (Some m2) as m'. revert m2 Heqm'.
  induction STORE; i.
  + clarify.
  + apply Mem.concrete_store in e0. rewrite e0.
    apply IHSTORE. assumption.
  + clarify.
Qed.