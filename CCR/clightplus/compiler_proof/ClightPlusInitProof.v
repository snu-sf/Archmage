From compcert Require Import Coqlib Errors Behaviors Integers Floats AST Globalenvs Ctypes Cop Clight Clightdefs.
Require Import CoqlibCCR.
Require Import ModSem.
Require Import ClightPlusExprgen ClightPlusgen ClightPlusSkel.

Lemma in_get_fnsems_decomp clight_prog fn sk l i :
  NoDup (List.map fst l) ->
  alist_find fn (get_fnsems clight_prog sk l) = Some i ->
  exists f, i = cfunU (decomp_func sk (get_ce clight_prog) f) /\ alist_find fn l = Some (Gfun (Internal f)).
Proof.
  ginduction l; i; ss. des_ifs_safe. inv H. destruct g as [[f|? ? ? ?]|v].
  - ss. des_ifs; cycle 1. { apply IHl; et. } esplits; et.
  - hexploit IHl; et. i. des. esplits; et. des_ifs.
    unfold rel_dec in Heq; ss. destruct dec; clarify.
    apply alist_find_some in H1. eapply in_map with (f:=fst) in H1. ss.
  - hexploit IHl; et. i. des. esplits; et. des_ifs.
    unfold rel_dec in Heq; ss. destruct dec; clarify.
    apply alist_find_some in H1. eapply in_map with (f:=fst) in H1. ss.
Qed.

Lemma get_sk_nodup l t : get_sk l = OK t -> NoDup (List.map fst t).
Proof.
  revert t. induction l; unfold get_sk; i; des_ifs. { econs. }
  2:{ apply IHl. unfold get_sk. ss. des_ifs. ss. bsimpl. des. clarify. }
  rewrite (List.map_map _ fst).
  replace (_ ∘ _) with (string_of_ident ∘ (@fst ident (globdef Clight.fundef type))).
  2:{ extensionalities. destruct H. ss. }
  rewrite <- (List.map_map _ string_of_ident).
  ss. des_ifs. econs.
  - ss. ii. apply n. bsimpl. des. clear - Heq Heq0 Heq1 Heq2 Heq3 Heq4 Heq5 H.
    ginduction l; ss; i. bsimpl. des. des_ifs. 2:{ right. eapply IHl; et. }
    ss. des.
    + left. bsimpl. des.
      assert (ident_of_string (string_of_ident (fst a0)) = fst a0).
      { unfold chk_ident in Heq0. des_ifs; ss; destruct Pos.eq_dec; clarify. }
      assert (ident_of_string (string_of_ident (fst a)) = fst a).
      { unfold chk_ident in Heq4. des_ifs; ss; destruct Pos.eq_dec; clarify. }
      rewrite <- H0. rewrite <- H1. f_equal; et.
    + right. bsimpl. des. apply IHl; et.
  - hexploit IHl. { ss. bsimpl. des. unfold get_sk. des_ifs. bsimpl. destruct list_norepet_dec; clarify. }
    i. rewrite (List.map_map _ fst) in H.
    replace (_ ∘ _) with (string_of_ident ∘ (@fst ident (globdef Clight.fundef type))) in H.
    2:{ extensionalities. destruct H0. ss. }
    rewrite List.map_map. et.
Qed.

Theorem in_tgt_prog_defs_decomp clight_prog mn md fn sk i :
  compile clight_prog mn = OK md ->
  alist_find fn (ModSem.fnsems (Mod.get_modsem md sk)) = Some i ->
  exists f, i = cfunU (decomp_func sk (get_ce clight_prog) f) /\ alist_find (ident_of_string fn) (prog_defs clight_prog) = Some (Gfun (Internal f)).
Proof.
  Local Opaque call_ban.
  unfold compile. i. des_ifs. ss.
  hexploit in_get_fnsems_decomp; et. { eapply get_sk_nodup; et. }
  i. des. clarify. esplits; et.
  clear -Heq H1. revert_until clight_prog.
  generalize (prog_defs clight_prog).
  induction l; i; ss. { unfold get_sk in Heq. des_ifs. }
  unfold get_sk in Heq. destruct list_norepet_dec; clarify.
  destruct forallb eqn: ?; clarify. ss.
  destruct (forallb chk_ident) eqn: ?; clarify. bsimpl. des.
  destruct (forallb chk_gd) eqn: ?; clarify. bsimpl. des.
  des_ifs.
  - unfold def_filter in Heq0.
    unfold rel_dec in Heq. ss. destruct dec; clarify. clear Heq.
    rewrite string_of_ident_of_string in H1.
    des_ifs; cycle 1.
    all: unfold rel_dec in Heq; ss; destruct dec; clarify.
  - exfalso.
    hexploit IHl; et. { unfold get_sk. inv l0. des_ifs. destruct list_norepet_dec; clarify. }
    i. apply alist_find_some in H. apply in_map with (f:=fst) in H.
    unfold rel_dec in Heq. ss. destruct dec; clarify. clear Heq.
    inv l0. et.
  - simpl in Heqb0. bsimpl. des.
    assert (ident_of_string (string_of_ident i) = i).
    { unfold chk_ident in Heqb0. destruct Pos.eq_dec; clarify. }
    clear Heqb Heq0. ss. des_ifs.
    { unfold rel_dec in *. ss. do 2 destruct dec; clarify. }
    eapply IHl; et. unfold get_sk. inv l0.
    bsimpl. des. des_ifs.
    destruct list_norepet_dec; clarify.
  - eapply IHl; et. unfold get_sk. inv l0. des_ifs.
    destruct list_norepet_dec; clarify.
Qed.

Theorem in_tgt_prog_main clight_prog mn md :
  compile clight_prog mn = OK md -> prog_main clight_prog = ident_of_string "main".
Proof. unfold compile. des_ifs. Qed.

Lemma tgt_genv_match_symb_def
    clight_prog md mn name b gd1 gd2
    (COMP: compile clight_prog mn = OK md)
    (GFSYM: Genv.find_symbol (Genv.globalenv clight_prog) name = Some b)
    (GFDEF: Genv.find_def (Genv.globalenv clight_prog) b = Some gd1)
    (INTGT: alist_find name (prog_defs clight_prog) = Some gd2)
:
    gd1 = gd2.
Proof.
  unfold compile, get_sk in COMP. des_ifs_safe. apply alist_find_some in INTGT.
  change (prog_defs clight_prog) with (AST.prog_defs clight_prog) in INTGT.
  bsimpl. des. destruct list_norepet_dec; clarify.
  hexploit prog_defmap_norepet; eauto; ss.
  i. apply Genv.find_def_symbol in H. des. clarify.
Qed.

Lemma tgt_genv_match_symb_def_by_blk
    clight_prog md mn name b gd
    (COMP: compile clight_prog mn = OK md)
    (GFSYM: Genv.find_symbol (Genv.globalenv clight_prog) name = Some b)
    (INTGT: alist_find name (prog_defs clight_prog) = Some gd)
:
    Genv.find_def (Genv.globalenv clight_prog) b = Some gd.
Proof.
  unfold compile, get_sk in COMP. des_ifs_safe. apply alist_find_some in INTGT.
  change (prog_defs clight_prog) with (AST.prog_defs clight_prog) in INTGT.
  bsimpl. des. destruct list_norepet_dec; clarify.
  hexploit prog_defmap_norepet; eauto; ss.
  i. apply Genv.find_def_symbol in H. des. clarify.
Qed.

(* These theorems are conditions should satisfied in closed program *)
Require Import ClightPlusMatchEnv.
Local Opaque in_dec.
Local Opaque ident_of_string.
Local Transparent call_ban.

Lemma compile_sk_incl clight_prog mn md str gd sk_mem:
  compile clight_prog mn = OK md ->
  mem_skel clight_prog = OK sk_mem ->
  In (str, gd) (Sk.canon (Sk.add sk_mem (Mod.sk md))) ->
  In (ident_of_string str, gd) (prog_defs clight_prog).
Proof.
  i. unfold compile in H. unfold get_sk in H. des_ifs. ss. bsimpl. des.
  let x := type of Sk.le_canon_rev in
  let y := eval red in x in
  eapply (Sk.le_canon_rev: x) in H1.
  ss. apply in_map with (f:=(map_fst ident_of_string)) in H1. ss.
  unfold Sk.add in H1. ss. rewrite map_app in H1. rewrite List.in_app_iff in H1.
  unfold mem_skel in H0. des_ifs. clear - H1 Heq1. revert_until clight_prog.
  generalize (prog_defs clight_prog). clear. induction l; i; ss; try tauto.
  des_ifs.
  - ss. bsimpl. des.
    + left. destruct a. ss. clarify. unfold chk_ident in Heq1. destruct Pos.eq_dec; clarify. rewrite <- e in H1. f_equal; et.
    + right. eapply IHl; et.
    + left. destruct a. ss. clarify. unfold chk_ident in Heq1. destruct Pos.eq_dec; clarify. rewrite <- e in H1. f_equal; et.
    + right. eapply IHl; et.
  - ss. bsimpl. des; clarify.
    + left. destruct a. ss. clarify.
      destruct in_dec; clarify. unfold mem_keywords in i0. ss.
      des; clarify; rewrite string_of_ident_of_string in *; f_equal; et.
    + right. eapply IHl; et.
    + right. eapply IHl; et.
  - ss. bsimpl. des; clarify.
    + right. eapply IHl; et.
    + left. destruct a. ss. clarify. unfold chk_ident in Heq1. destruct Pos.eq_dec; clarify. rewrite <- e in H1. f_equal; et.
    + right. eapply IHl; et.
  - ss. bsimpl. des; clarify.
    + right. eapply IHl; et.
    + right. eapply IHl; et.
Qed.

Lemma compile_tgt_blk_exists clight_prog mn md idx str sk_mem:
  compile clight_prog mn = OK md ->
  mem_skel clight_prog = OK sk_mem ->
  SkEnv.blk2id (load_skenv (Sk.canon (Sk.add sk_mem (Mod.sk md)))) idx = Some str ->
  exists tb, Genv.find_symbol (Genv.globalenv clight_prog) (ident_of_string str) = Some tb.
Proof.
  i. hexploit in_env_in_sk; et. i. des. clear H1.
  apply Genv.find_symbol_exists with (g:=def).
  eapply compile_sk_incl; et.
Qed.

Lemma compile_sk_wf clight_prog mn md sk_mem:
  compile clight_prog mn = OK md ->
  mem_skel clight_prog = OK sk_mem ->
  Sk.wf (Sk.canon (Sk.add sk_mem (Mod.sk md))).
Proof.
  i. apply Sk.wf_canon. unfold Sk.wf. ss. rewrite CoqlibC.NoDup_norepet.
  unfold Sk.add. ss. rewrite List.map_app. rewrite list_norepet_app.
  splits.
  - unfold mem_skel in H0. unfold compile, get_sk in H. des_ifs. destruct list_norepet_dec; clarify. bsimpl.
    des. clear -l Heq1. induction (prog_defs clight_prog); i; ss. { econs. }
    inv l. bsimpl. des. destruct in_dec; ss; et. destruct a. ss.
    econs; et. ii. apply H1. clear -H i.
    induction l0; i; ss. destruct in_dec; ss; clarify. 2:{ right. et. }
    destruct a; ss. des; clarify; et.
  - unfold compile, get_sk in H. des_ifs. destruct list_norepet_dec; clarify. ss.
    clear -l Heq1. revert_until clight_prog. generalize (prog_defs clight_prog).
    clear clight_prog. induction l; i; ss. { econs. }
    inv l0. des_ifs; et. ss. bsimpl. des. econs; et.
    ii. apply H1. destruct a. ss. unfold chk_ident in Heq1. destruct Pos.eq_dec; clarify.
    clear - H Heq3 e. induction l; i; ss. des_ifs; et. ss. bsimpl. des; et. destruct a. ss.
    left. rewrite e. unfold chk_ident in Heq3. destruct Pos.eq_dec; clarify. rewrite e0. f_equal; et.
  - ii. unfold compile, get_sk in H. des_ifs. ss. unfold mem_skel in H0. des_ifs.
    bsimpl. des. clear - Heq1 Heq3 H1 H2. revert_until clight_prog. generalize (prog_defs clight_prog).
    clear clight_prog. induction l; i; ss. bsimpl. des. des_ifs; et.
    + destruct in_dec; clarify. clear -Heq3 Heq i. destruct a; ss. des_ifs; destruct in_dec; des; clarify; ss; et.
    + ss. bsimpl. des; et. clarify. destruct in_dec; clarify. clear - Heq1 n H1. induction l; ss.
      destruct in_dec; clarify. ss. destruct H1; et. destruct a; destruct a0; ss. unfold chk_ident in Heq1.
      destruct Pos.eq_dec; clarify. clear Heq1. des; try tauto; clarify; rewrite string_of_ident_of_string in *; rewrite <- H in *; et.
    + ss. des; et. clarify. clear - Heq1 Heq0 Heq2 H2. induction l; ss. bsimpl. des.
      des_ifs; et. ss. bsimpl. des; et.
      clear - Heq0 Heq Heq1 Heq2 H2.
      destruct a; destruct a0; ss. unfold chk_ident in Heq1. destruct Pos.eq_dec in Heq1; clarify.
      des_ifs; try do 2 destruct in_dec; clarify.
      all: ss; des; clarify; rewrite H2 in *; rewrite e in *; et.
Qed.

Lemma compile_match_genv clight_prog mn md sk_mem:
  compile clight_prog mn = OK md ->
  mem_skel clight_prog = OK sk_mem ->
  match_ge (Sk.canon (Sk.add sk_mem (Mod.sk md))) (Genv.globalenv clight_prog).
Proof.
  i. econs.
  - eapply compile_sk_wf; et.
  - i. hexploit compile_sk_wf; et. i.
    hexploit load_skenv_wf; et. i. unfold SkEnv.wf in H3. red in H3. rewrite H3 in H1.
    hexploit compile_tgt_blk_exists; et. i. clear H3.
    des. unfold map_blk. destruct le_dec; cycle 1.
    { replace (Init.Nat.pred _) with idx by nia. ss. rewrite H1.
      des_ifs. unfold fundef in *. clarify. }
    exfalso. assert (List.length (Sk.canon (Sk.add sk_mem (Mod.sk md))) <= idx) by nia.
    Local Transparent load_skenv. ss. uo. des_ifs.
    apply nth_error_None in H3. clarify.
  - i. assert (SkEnv.blk2id (load_skenv (Sk.canon (Sk.add sk_mem (Mod.sk md)))) n = Some s) by now ss; uo; des_ifs.
    hexploit compile_tgt_blk_exists; et. i. des.
    assert (Genv.find_symbol (Genv.globalenv clight_prog) (ident_of_string s) = Some (map_blk (Sk.canon (Sk.add sk_mem (Mod.sk md))) (Genv.globalenv clight_prog) (Pos.of_succ_nat n))).
    { unfold map_blk. destruct le_dec; cycle 1.
      { replace (Init.Nat.pred _) with n by nia. rewrite H2.
        des_ifs. unfold fundef in *. clarify. }
      exfalso. assert (List.length (Sk.canon (Sk.add sk_mem (Mod.sk md))) <= n) by nia. ss. uo. des_ifs.
      apply nth_error_None in H4. clarify. }
    clear H2.
    assert (Maps.PTree.get (ident_of_string s) (prog_defmap clight_prog) = Some gd).
    { unfold prog_defmap. ss. apply Maps.PTree_Properties.of_list_norepet; et.
      { unfold compile, get_sk in H. des_ifs. destruct list_norepet_dec; clarify. }
      apply nth_error_in in H1. eapply compile_sk_incl; et. }
    rewrite Genv.find_def_symbol in H2. des. clarify.
Qed.

Require Import ClightPlusMem0 ClightPlusMemSim.
From compcert Require Import Memory Maps Values.

Lemma store_init_data_list_aligned sk m b p il m' :
  store_init_data_list sk m b p il = Some m' -> Genv.init_data_list_aligned p il.
Proof.
  Local Transparent Mem.store.
  ginduction il; ss. i. des_ifs. split; et. unfold store_init_data, Mem.store in Heq.
  des_ifs; unfold Mem.valid_access in *; ss; des; et.
  red. exists p. nia.
Qed.

Lemma store_init_data_list_free_idents sk m b p il m' :
  store_init_data_list sk m b p il = Some m' -> (forall symb ofs, In (Init_addrof symb ofs) il -> exists idx, SkEnv.id2blk (load_skenv sk) (string_of_ident symb) = Some idx).
Proof.
  ginduction il; ss. i. des_ifs. des; et. clarify.
  unfold store_init_data in Heq. des_ifs. ss. et.
Qed.

Lemma store_init_data_list_exists sk m b p il :
       Mem.range_perm m b p (p + init_data_list_size il) Cur Writable ->
       Genv.init_data_list_aligned p il ->
       (forall symb ofs,
        In (Init_addrof symb ofs) il ->
        exists idx, SkEnv.id2blk (load_skenv sk) (string_of_ident symb) = Some idx) ->
        exists m' : mem, store_init_data_list sk m b p il = Some m'.
Proof.
  ginduction il; et. i. ss. des.
  destruct store_init_data eqn:?; et.
  - apply IHil; et. ii. red in H. generalize (init_data_size_pos a). i.
    hexploit (H ofs); try nia. i.
    unfold store_init_data, Mem.store in Heqo. des_ifs.
  - generalize (init_data_size_pos a). i.
    generalize (init_data_list_size_pos il). i.
    unfold store_init_data, Mem.store in Heqo. des_ifs.
    all: try solve [exfalso; apply n; red; split; et; ii; apply H; ss; nia].
    + exfalso; apply n0; red; split; et. ii; apply H. unfold Mptr in H5. ss. des_ifs. ss. nia.
    + exfalso. ss. hexploit H1; et. i. des. clarify.
Qed.

Lemma alloc_global_exists sk:
  forall m idg,
  match idg with
  | Gfun f => True
  | Gvar v =>
        Genv.init_data_list_aligned 0 v.(gvar_init)
        /\ forall symb ofs, In (Init_addrof symb ofs) v.(gvar_init) -> exists idx, SkEnv.id2blk (load_skenv sk) (string_of_ident symb) = Some idx
  end
  -> exists m', alloc_global sk m idg = Some m'.
Proof.
  Local Transparent Mem.alloc.
  i. des_ifs.
  - ss. unfold Mem.drop_perm. des_ifs; et. exfalso. apply n.
    unfold Mem.range_perm, Mem.perm. ss. i. rewrite PMap.gss.
    destruct zle; destruct zlt; try nia; ss. econs.
  Local Opaque Mem.alloc.
  - des. ss. destruct Mem.alloc eqn:?.
    set (sz := init_data_list_size (gvar_init v)).
    assert (P1: Mem.range_perm m0 b 0 sz Cur Freeable) by (red; intros; eapply Mem.perm_alloc_2; eauto).
    hexploit Genv.store_zeros_exists; et.
    { ii. red in P1. change sz with (0 + sz)%Z in P1. apply P1 in H1. unfold Mem.perm, Mem.perm_order' in *. des_ifs. rewrite Heq0 in Heq. clarify. inv H1; econs. clarify. }
    i. des. rewrite H1.
    assert (P2: Mem.range_perm m' b 0 sz Cur Freeable).
    { red; intros. erewrite <- Genv.store_zeros_perm by eauto. eauto. }
    hexploit store_init_data_list_exists; ss; et.
    { ii. eapply Mem.perm_implies; try apply P2; et. econs. }
    i. des. des_ifs.
    unfold Mem.drop_perm. des_ifs; et.
    exfalso. apply n. clear - P2 Heq.
    assert (init_data_list_size (gvar_init v) <= sz)%Z by nia. clearbody sz.
    set 0%Z in Heq. assert (0 <= z)%Z by nia. clearbody z.
    set (gvar_init v) in *. ginduction l; ss; i; clarify.
    des_ifs. generalize (init_data_size_pos a). i. generalize (init_data_list_size_pos l). i.
    hexploit IHl. 2: apply Heq. all: et; try nia. unfold store_init_data, Mem.store in *.
    des_ifs.
Qed.

Lemma load_mem_exists sk
  (COND: forall id v, In (id, Gvar v) sk -> Genv.init_data_list_aligned 0 (gvar_init v) /\ (forall symb ofs, In (Init_addrof symb ofs) (gvar_init v) -> exists idx, SkEnv.id2blk (load_skenv sk) (string_of_ident symb) = Some idx)) :
  exists m, load_mem sk = Some m.
Proof.
  unfold load_mem. revert COND. generalize Mem.empty. generalize sk at 1 4.
  induction sk0; i; ss; et. destruct a. hexploit (alloc_global_exists sk m g); et.
  { des_ifs. et. } i. des. des_ifs. et.
Qed.

Lemma load_mem_inversion sk m (SUCC: load_mem sk = Some m):
  forall id v, In (id, Gvar v) sk ->
    Genv.init_data_list_aligned 0 (gvar_init v) /\ (forall symb ofs, In (Init_addrof symb ofs) (gvar_init v) -> exists idx, SkEnv.id2blk (load_skenv sk) (string_of_ident symb) = Some idx).
Proof.
  unfold load_mem in SUCC. set (sk_forenv:=sk) in SUCC at 1. change sk with sk_forenv at 2.
  revert m SUCC. generalize sk_forenv. generalize Mem.empty.
  induction sk; ss. i. des_ifs. des; et. clarify.
  unfold alloc_global in Heq. des_ifs.
  hexploit store_init_data_list_aligned; et. i. split; et.
  i. hexploit store_init_data_list_free_idents; et.
Qed.

Definition bytes_of_init_data sk (i : init_data) : list memval :=
  match i with
  | Init_int8 n => inj_bytes (encode_int 1 (Int.unsigned n))
  | Init_int16 n => inj_bytes (encode_int 2 (Int.unsigned n))
  | Init_int32 n => inj_bytes (encode_int 4 (Int.unsigned n))
  | Init_int64 n => inj_bytes (encode_int 8 (Int64.unsigned n))
  | Init_float32 n => inj_bytes (encode_int 4 (Int.unsigned (Float32.to_bits n)))
  | Init_float64 n => inj_bytes (encode_int 8 (Int64.unsigned (Float.to_bits n)))
  | Init_space n => repeat (Byte Byte.zero) (Z.to_nat n)
  | Init_addrof symb ofs =>
      match SkEnv.id2blk (load_skenv sk) (string_of_ident symb) with
      | Some idx => inj_value (if Archi.ptr64 then Q64 else Q32) (Vptr (Pos.of_succ_nat idx) ofs)
      | None => repeat Undef (if Archi.ptr64 then 8 else 4)
      end
  end.

Fixpoint bytes_of_init_data_list sk (il : list init_data) : list memval :=
  match il with
  | [] => []
  | i :: il0 => bytes_of_init_data sk i ++ bytes_of_init_data_list sk il0
  end.

Lemma src_bytes_of_init_data_list_len sk il : Z.of_nat (List.length (bytes_of_init_data_list sk il)) = init_data_list_size il.
Proof.
  induction il; i; ss. rewrite app_length. rewrite <- IHil. unfold bytes_of_init_data.
  des_ifs; ss.
  all: try (rewrite length_inj_bytes; rewrite encode_int_length; nia).
  - rewrite repeat_length. nia.
  - des_ifs. nia.
  - des_ifs. nia.
Qed.

Lemma tgt_bytes_of_init_data_list_len ge il : Z.of_nat (List.length (Genv.bytes_of_init_data_list (F:=Clight.fundef) (V:=type) ge il)) = init_data_list_size il.
Proof.
  induction il; i; ss. rewrite app_length. rewrite <- IHil. unfold Genv.bytes_of_init_data.
  des_ifs; ss.
  all: try (rewrite length_inj_bytes; rewrite encode_int_length; nia).
  - rewrite repeat_length. nia.
  - des_ifs. nia.
  - des_ifs. nia.
Qed.

Lemma addrof_is_wf_in_global clight_prog sk_mem sk :
  mem_skel clight_prog = OK sk_mem ->
  get_sk (prog_defs clight_prog) = OK sk ->
  forall s v symb ofs, In (s, Gvar v) (Sk.canon (Sk.add sk_mem sk)) ->
    In (Init_addrof symb ofs) (gvar_init v)
    -> SkEnv.id2blk (load_skenv (Sk.canon (Sk.add sk_mem sk))) (string_of_ident symb) <> None /\ chk_ident symb = true.
Proof.
  i. unfold mem_skel in H. des_ifs. revert m H1. set (List.map _ _) as sk_mem.
  i. red in m. hexploit m; et. i. des. hexploit H0; et. i. des.
  rewrite H3. split; et. generalize Sk.le_canon_rev. i. ss. apply H4 in H1. apply in_app in H1.
  clear - H1 H2 Heq. unfold get_sk in Heq. des_ifs. bsimpl. des.
  - unfold sk_mem in H1. rewrite in_map_iff in H1. des. destruct x; ss; clarify.
    apply filter_In in H0. des. rewrite forallb_forall in Heq3. apply Heq3 in H0. ss.
    destruct in_dec; clarify. destruct in_dec; clarify. ss. des; clarify; ss; et. exfalso. et.
  - clear sk_mem. rewrite forallb_forall in Heq2.
    rewrite in_map_iff in H1. des. destruct x; ss; clarify.
    apply in_map with (f:=snd) in H0. ss. apply Heq2 in H0. ss. des_ifs.
    ss. rewrite forallb_forall in H0. apply H0 in H2. ss.
Qed.

Lemma match_bytes_of_init_data sk tge i
  (MGE: match_ge sk tge)
  (VALID: forall symb ofs, i = Init_addrof symb ofs -> SkEnv.id2blk (load_skenv sk) (string_of_ident symb) <> None /\ chk_ident symb = true)
:
  List.map (map_memval sk tge) (bytes_of_init_data sk i) = Genv.bytes_of_init_data tge i.
Proof.
  i. inv MGE. unfold bytes_of_init_data. des_ifs.
  - ss. induction (Z.to_nat z); ss. f_equal; et.
  - apply MGE0 in Heq. ss. hexploit VALID; et. i. des.
    unfold chk_ident in H0. destruct Pos.eq_dec; clarify.
    rewrite <- e in Heq. des_ifs.
  - hexploit VALID; et. i. des. clarify.
Qed.

Lemma match_bytes_of_init_data_list sk tge il
  (MGE: match_ge sk tge)
  (VALID: forall symb ofs, In (Init_addrof symb ofs) il -> SkEnv.id2blk (load_skenv sk) (string_of_ident symb) <> None /\ chk_ident symb = true)
:
  List.map (map_memval sk tge) (bytes_of_init_data_list sk il) = Genv.bytes_of_init_data_list tge il.
Proof.
  set il as il'. assert (List.incl il' il) by refl. clearbody il'.
  induction il'; ss. rewrite map_app. f_equal; cycle 1.
  { apply IHil'. etrans; et. ii. ss. et. }
  apply match_bytes_of_init_data; et. i. ss.
  apply VALID with (ofs := ofs). apply H. clarify. ss. et.
Qed.

Lemma match_bytes_of_gvar_init clight_prog tge sk_mem sk
  (GCOMP: mem_skel clight_prog = OK sk_mem)
  (SK: get_sk (prog_defs clight_prog) = OK sk)
  (MGE: match_ge (Sk.canon (Sk.add sk_mem sk)) tge)
:
  forall s v, In (s, Gvar v) (Sk.canon (Sk.add sk_mem sk)) ->
  List.map (map_memval (Sk.canon (Sk.add sk_mem sk)) tge) (bytes_of_init_data_list (Sk.canon (Sk.add sk_mem sk)) (gvar_init v)) = Genv.bytes_of_init_data_list tge (gvar_init v).
Proof.
  i. apply match_bytes_of_init_data_list; et. i. hexploit addrof_is_wf_in_global; et.
Qed.

Lemma store_zero_cnt m0 b m1 p il:
  store_zeros m0 b p (init_data_list_size il) = Some m1 ->
  forall ofs, ((Mem.mem_contents m1) !! b) !! ofs = (Mem.setN (repeat (Byte Byte.zero) (Z.to_nat (init_data_list_size il))) p ((Mem.mem_contents m0) !! b)) !! ofs.
Proof.
  i. symmetry in H. apply R_store_zeros_correct in H.
  remember (Some _) in H.
  ginduction H; i; et; clarify.
  { replace (Z.to_nat n) with 0 by nia. ss. }
  hexploit IHR_store_zeros; et. i. rewrite H0.
  apply Mem.store_mem_contents in e0. rewrite e0.
  replace (p + 1)%Z with (p + Z.of_nat (List.length (encode_val Mint8unsigned Vzero)))%Z by ss.
  rewrite PMap.gss. rewrite <- Mem.setN_concat. repeat f_equal.
  replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by nia. ss.
Qed.

Lemma tgt_store_zero_list (ge: Genv.t fundef type) il m0 b m1 m2 :
  store_zeros m0 b 0 (init_data_list_size il) = Some m1 ->
  Genv.store_init_data_list ge m1 b 0 il = Some m2 ->
  forall ofs, ((Mem.mem_contents m2) !! b) !! ofs = (Mem.setN (Genv.bytes_of_init_data_list ge il) 0 ((Mem.mem_contents m0) !! b)) !! ofs.
Proof.
  i. revert ofs.
  generalize (store_zero_cnt m0 b m1 0 il H). i.
  assert (Mem.range_perm m0 b 0 (0 + init_data_list_size il) Cur Writable).
  { clear -H. set 0%Z in *. clearbody z. symmetry in H. apply R_store_zeros_correct in H.
    revert H. remember (Some _). generalize (init_data_list_size il).
    i. ginduction H; i; ss; clarify.
    { generalize (init_data_list_size_pos il). ii. nia. }
    hexploit IHR_store_zeros; et. ii. unfold Mem.store in e0. des_ifs.
    destruct (dec p ofs); cycle 1. { red in H0. unfold Mem.perm in *. ss. apply H0. nia. }
    clarify. clear - v. red in v. des. apply v. ss. nia. }
  clear H. set 0%Z in *. clearbody z. ginduction il; i; ss; clarify.
  des_ifs.
  assert (exists m', Genv.store_init_data ge m0 b z a = Some m').
  { unfold Genv.store_init_data. generalize (init_data_list_size_pos il). i.
    des_ifs; et.
    - ss. unfold Mem.store in *. des_ifs; et. exfalso. apply n.
      unfold Mem.valid_access in *. des. split; et. ii. apply H2. ss. nia.
    - ss. unfold Mem.store in *. des_ifs; et. exfalso. apply n.
      unfold Mem.valid_access in *. des. split; et. ii. apply H2. ss. nia.
    - ss. unfold Mem.store in *. des_ifs; et. exfalso. apply n.
      unfold Mem.valid_access in *. des. split; et. ii. apply H2. ss. nia.
    - ss. unfold Mem.store in *. des_ifs; et. exfalso. apply n.
      unfold Mem.valid_access in *. des. split; et. ii. apply H2. ss. nia.
    - ss. unfold Mem.store in *. des_ifs; et. exfalso. apply n.
      unfold Mem.valid_access in *. des. split; et. ii. apply H2. ss. nia.
    - ss. unfold Mem.store in *. des_ifs; et. exfalso. apply n.
      unfold Mem.valid_access in *. des. split; et. ii. apply H2. ss. nia.
    - ss. unfold Mem.store in *. des_ifs; et. exfalso. apply n.
      unfold Mem.valid_access in *. des. split; et. ii. apply H2. ss. nia.
    - ss. des_ifs. }
  des. assert ((exists z, Init_space z = a) \/ ~ (exists z, Init_space z = a)).
  { destruct a; et; right; ii; des; clarify. }
  generalize (init_data_list_size_pos il).
  generalize (init_data_size_pos a). i.
  des.
  - clarify. ss. clarify.
    assert (exists m'', store_zeros m' b z (Z.max z0 0) = Some m'').
    { apply Genv.store_zeros_exists. ii. apply H2. nia. }
    des. generalize (store_zero_cnt m' b m'' z [Init_space z0]). i. ss. rewrite Z.add_0_r in H3. spc H3.
    hexploit (IHil ge m''); et.
    { i. rewrite H1. destruct (zindex_surj ofs0). clarify.
      destruct ((x <? z) || (x >=? z + (Z.max z0 0) + (init_data_list_size il)))%Z eqn: e1.
      - generalize Mem.setN_outside. i. unfold ZMap.get in *. rewrite !H6. 2,3: rewrite repeat_length; nia.
        rewrite H3. rewrite H6; et. rewrite repeat_length; nia.
      - generalize setN_inside. i.
        edestruct H6 as [x0 [X X']];[|unfold ZMap.get in *; rewrite X'].
        { rewrite repeat_length. nia. }
        destruct ((x <? z + (Z.max z0 0)) || (x >=? z + (Z.max z0 0) + (init_data_list_size il)))%Z eqn: e2.
        + generalize Mem.setN_outside. i. unfold ZMap.get in *. rewrite !H7.
          2: rewrite repeat_length; nia. rewrite H3.
          edestruct H6 as [x1 [X'' X''']];[|unfold ZMap.get in *; rewrite X'''].
          { rewrite repeat_length. nia. } apply nth_error_in in X, X''. apply repeat_spec in X, X''.
          clarify.
        + edestruct H6 as [x1 [X'' X''']];[|unfold ZMap.get in *; rewrite X'''].
          { rewrite repeat_length. nia. } apply nth_error_in in X, X''. apply repeat_spec in X, X''.
          clarify. }
    { ii. rewrite <- Genv.store_zeros_perm; et. apply H2. nia. }
    i. rewrite H6. destruct (zindex_surj ofs). clarify.
    destruct ((x <? z + (Z.max z0 0)) || (x >=? z + (Z.max z0 0) + (init_data_list_size il)))%Z eqn: e1.
    + generalize Mem.setN_outside. i. generalize (tgt_bytes_of_init_data_list_len ge). i.
      rewrite <- H8 in e1. unfold ZMap.get in *. rewrite H7; try nia.
      rewrite H3.
      destruct ((x <? z) || (x >=? z + (Z.max z0 0) + (init_data_list_size il)))%Z eqn: e2.
      * generalize Mem.setN_outside. i. unfold ZMap.get in *. rewrite !H7; et.
        all: try rewrite app_length; rewrite repeat_length; nia.
      * rewrite <- H8 in e2. generalize setN_inside. i. unfold ZMap.get in *.
        edestruct H9 as [x0 [X X']];[| rewrite X'].
        { rewrite repeat_length. nia. }
        edestruct H9 as [x1 [X'' X''']];[| rewrite X'''].
        { rewrite app_length. rewrite repeat_length. nia. }
        edestruct nth_error_Some. hexploit H10. { rewrite X. et. } i.
        rewrite nth_error_app1 in X''. 2:{ rewrite repeat_length in *. nia. }
        apply nth_error_in in X, X''. apply repeat_spec in X, X''. clarify.
    + generalize setN_inside. i. unfold ZMap.get in *. generalize (tgt_bytes_of_init_data_list_len ge). i.
      rewrite <- H8 in e1.
      edestruct H7 as [x0 [X X']];[| rewrite X']; try nia.
      edestruct H7 as [x1 [X'' X''']];[| rewrite X'''].
      { rewrite app_length. rewrite repeat_length. nia. }
      edestruct nth_error_Some. hexploit H9. { rewrite X. et. } i.
      rewrite nth_error_app2 in X''. 2:{ rewrite repeat_length in *. nia. }
      rewrite repeat_length in X''.
      replace (Z.to_nat (x - (z + Z.max z0 0))) with (Z.to_nat (x - z) - Z.to_nat z0) in X by nia. clarify.
  - hexploit (IHil ge m'); et; cycle 1.
    { clear - Heq H2 H. unfold Genv.store_init_data, Mem.store in *. des_ifs; ss.
      all: try solve [ii; red; ss; apply H2; nia].
      ii. red. ss. des_ifs. apply H2. nia. }
    { i. rewrite H6. clear -H H3.
      unfold Genv.store_init_data, Mem.store in *. des_ifs; ss. 7:{ exfalso. et. }
      all: rewrite PMap.gss; rewrite Mem.setN_concat; et.
      des_ifs. }
    clear - Heq H H1 H2 H H3 H4 H5. i. destruct (zindex_surj ofs). clarify.
    destruct ((x >=? z + init_data_size a) && (x <? z + init_data_size a + (init_data_list_size il)))%Z eqn: e1.
    + generalize setN_inside. i. unfold ZMap.get in *.
      edestruct H0 as [x0 [X X']];[| rewrite X'].
      { rewrite repeat_length. nia. }
      apply nth_error_in in X. apply repeat_spec in X. clarify.
      generalize Mem.setN_outside; i; unfold ZMap.get in *.
      unfold Genv.store_init_data, Mem.store in *. des_ifs; ss. 7:{ exfalso. et. }
      all: try (rewrite !PMap.gss in *; rewrite H6;[|rewrite length_inj_bytes; rewrite encode_int_length; nia]).
      all: try (rewrite H1; edestruct H0 as [x1 [X'' X''']];[| rewrite X''']; [rewrite repeat_length; nia|]).
      all: try (apply nth_error_in in X''; apply repeat_spec in X''; clarify).
      rewrite !PMap.gss in *. rewrite H6. 2:{ des_ifs. ss. nia. } rewrite H1. des_ifs.
      edestruct H0 as [x1 [X'' X''']];[| rewrite X''']; [rewrite repeat_length; nia|].
      apply nth_error_in in X''; apply repeat_spec in X''; clarify.
    + generalize Mem.setN_outside. i. unfold ZMap.get in *. rewrite H0. 2:{ rewrite repeat_length. nia. }
      destruct ((x <? z + init_data_size a) && (z <=? x))%Z eqn:?; clarify.
      * generalize setN_inside. i. unfold ZMap.get in *.
        unfold Genv.store_init_data, Mem.store in *. des_ifs; ss. 7:{ exfalso. et. }
        all: try (rewrite !PMap.gss; edestruct H6 as [x0 [X X']];[| rewrite X']; [rewrite length_inj_bytes; rewrite encode_int_length; nia|]).
        all: try (edestruct H6 as [x1 [X'' X''']];[| rewrite X''']; [rewrite length_inj_bytes; rewrite encode_int_length; nia|]; clarify).
        des_ifs. rewrite !PMap.gss. edestruct H6 as [x0 [X X']];[| rewrite X']. { ss. nia. }
        edestruct H6 as [x1 [X'' X''']];[| rewrite X''']. { ss. nia. }
        clarify.
      * unfold Genv.store_init_data, Mem.store in *. des_ifs; ss. 7:{ exfalso. et. }
        all: try (rewrite !PMap.gss; rewrite !H0; [>|rewrite length_inj_bytes; rewrite encode_int_length; nia..]).
        all: try (rewrite !H1; rewrite !H0; [>|rewrite repeat_length; nia..]; et).
        rewrite !PMap.gss; rewrite !H0; [>|des_ifs; ss; nia..].
        rewrite !H1; rewrite !H0; et. des_ifs. rewrite repeat_length; nia.
Qed.

Lemma src_store_zero_list (sk: Sk.t) il m0 b m1 m2 :
  store_zeros m0 b 0 (init_data_list_size il) = Some m1 ->
  store_init_data_list sk m1 b 0 il = Some m2 ->
  forall ofs, ((Mem.mem_contents m2) !! b) !! ofs = (Mem.setN (bytes_of_init_data_list sk il) 0 ((Mem.mem_contents m0) !! b)) !! ofs.
Proof.
  i. revert ofs.
  generalize (store_zero_cnt m0 b m1 0 il H). i.
  assert (Mem.range_perm m0 b 0 (0 + init_data_list_size il) Cur Writable).
  { clear -H. set 0%Z in *. clearbody z. symmetry in H. apply R_store_zeros_correct in H.
    revert H. remember (Some _). generalize (init_data_list_size il).
    i. ginduction H; i; ss; clarify.
    { generalize (init_data_list_size_pos il). ii. nia. }
    hexploit IHR_store_zeros; et. ii. unfold Mem.store in e0. des_ifs.
    destruct (dec p ofs); cycle 1. { red in H0. unfold Mem.perm in *. ss. apply H0. nia. }
    clarify. clear - v. red in v. des. apply v. ss. nia. }
  clear H. set 0%Z in *. clearbody z. ginduction il; i; ss; clarify.
  des_ifs.
  assert (exists m', store_init_data sk m0 b z a = Some m').
  { unfold store_init_data. generalize (init_data_list_size_pos il). i.
    des_ifs; et.
    - ss. unfold Mem.store in *. des_ifs; et. exfalso. apply n.
      unfold Mem.valid_access in *. des. split; et. ii. apply H2. ss. nia.
    - ss. unfold Mem.store in *. des_ifs; et. exfalso. apply n.
      unfold Mem.valid_access in *. des. split; et. ii. apply H2. ss. nia.
    - ss. unfold Mem.store in *. des_ifs; et. exfalso. apply n.
      unfold Mem.valid_access in *. des. split; et. ii. apply H2. ss. nia.
    - ss. unfold Mem.store in *. des_ifs; et. exfalso. apply n.
      unfold Mem.valid_access in *. des. split; et. ii. apply H2. ss. nia.
    - ss. unfold Mem.store in *. des_ifs; et. exfalso. apply n.
      unfold Mem.valid_access in *. des. split; et. ii. apply H2. ss. nia.
    - ss. unfold Mem.store in *. des_ifs; et. exfalso. apply n.
      unfold Mem.valid_access in *. des. split; et. ii. apply H2. ss. nia.
    - ss. unfold Mem.store in *. des_ifs; et. exfalso. apply n0.
      unfold Mem.valid_access in *. des. split; et. ii. apply H2. ss. nia.
    - ss. des_ifs. }
  des. assert ((exists z, Init_space z = a) \/ ~ (exists z, Init_space z = a)).
  { destruct a; et; right; ii; des; clarify. }
  generalize (init_data_list_size_pos il).
  generalize (init_data_size_pos a). i.
  des.
  - clarify. ss. clarify.
    assert (exists m'', store_zeros m' b z (Z.max z0 0) = Some m'').
    { apply Genv.store_zeros_exists. ii. apply H2. nia. }
    des. generalize (store_zero_cnt m' b m'' z [Init_space z0]). i. ss. rewrite Z.add_0_r in H3. spc H3.
    hexploit (IHil sk m''); et.
    { i. rewrite H1. destruct (zindex_surj ofs0). clarify.
      destruct ((x <? z) || (x >=? z + (Z.max z0 0) + (init_data_list_size il)))%Z eqn: e1.
      - generalize Mem.setN_outside. i. unfold ZMap.get in *. rewrite !H6. 2,3: rewrite repeat_length; nia.
        rewrite H3. rewrite H6; et. rewrite repeat_length; nia.
      - generalize setN_inside. i.
        edestruct H6 as [x0 [X X']];[|unfold ZMap.get in *; rewrite X'].
        { rewrite repeat_length. nia. }
        destruct ((x <? z + (Z.max z0 0)) || (x >=? z + (Z.max z0 0) + (init_data_list_size il)))%Z eqn: e2.
        + generalize Mem.setN_outside. i. unfold ZMap.get in *. rewrite !H7.
          2: rewrite repeat_length; nia. rewrite H3.
          edestruct H6 as [x1 [X'' X''']];[|unfold ZMap.get in *; rewrite X'''].
          { rewrite repeat_length. nia. } apply nth_error_in in X, X''. apply repeat_spec in X, X''.
          clarify.
        + edestruct H6 as [x1 [X'' X''']];[|unfold ZMap.get in *; rewrite X'''].
          { rewrite repeat_length. nia. } apply nth_error_in in X, X''. apply repeat_spec in X, X''.
          clarify. }
    { ii. rewrite <- Genv.store_zeros_perm; et. apply H2. nia. }
    i. rewrite H6. destruct (zindex_surj ofs). clarify.
    destruct ((x <? z + (Z.max z0 0)) || (x >=? z + (Z.max z0 0) + (init_data_list_size il)))%Z eqn: e1.
    + generalize Mem.setN_outside. i. generalize (src_bytes_of_init_data_list_len sk). i.
      rewrite <- H8 in e1. unfold ZMap.get in *. rewrite H7; try nia.
      rewrite H3.
      destruct ((x <? z) || (x >=? z + (Z.max z0 0) + (init_data_list_size il)))%Z eqn: e2.
      * generalize Mem.setN_outside. i. unfold ZMap.get in *. rewrite !H7; et.
        all: try rewrite app_length; rewrite repeat_length; nia.
      * rewrite <- H8 in e2. generalize setN_inside. i. unfold ZMap.get in *.
        edestruct H9 as [x0 [X X']];[| rewrite X'].
        { rewrite repeat_length. nia. }
        edestruct H9 as [x1 [X'' X''']];[| rewrite X'''].
        { rewrite app_length. rewrite repeat_length. nia. }
        edestruct nth_error_Some. hexploit H10. { rewrite X. et. } i.
        rewrite nth_error_app1 in X''. 2:{ rewrite repeat_length in *. nia. }
        apply nth_error_in in X, X''. apply repeat_spec in X, X''. clarify.
    + generalize setN_inside. i. unfold ZMap.get in *. generalize (src_bytes_of_init_data_list_len sk). i.
      rewrite <- H8 in e1.
      edestruct H7 as [x0 [X X']];[| rewrite X']; try nia.
      edestruct H7 as [x1 [X'' X''']];[| rewrite X'''].
      { rewrite app_length. rewrite repeat_length. nia. }
      edestruct nth_error_Some. hexploit H9. { rewrite X. et. } i.
      rewrite nth_error_app2 in X''. 2:{ rewrite repeat_length in *. nia. }
      rewrite repeat_length in X''.
      replace (Z.to_nat (x - (z + Z.max z0 0))) with (Z.to_nat (x - z) - Z.to_nat z0) in X by nia. clarify.
  - hexploit (IHil sk m'); et; cycle 1.
    { clear - Heq H2 H. unfold store_init_data, Mem.store in *. des_ifs; ss.
      all: try solve [ii; red; ss; apply H2; nia].
      ii. red. ss. des_ifs. apply H2. nia. }
    { i. rewrite H6. clear -H H3.
      unfold store_init_data, Mem.store in *. des_ifs; ss. 7:{ exfalso. et. }
      all: rewrite PMap.gss; rewrite Mem.setN_concat; et.
      des_ifs. }
    clear - Heq H H1 H2 H H3 H4 H5. i. destruct (zindex_surj ofs). clarify.
    destruct ((x >=? z + init_data_size a) && (x <? z + init_data_size a + (init_data_list_size il)))%Z eqn: e1.
    + generalize setN_inside. i. unfold ZMap.get in *.
      edestruct H0 as [x0 [X X']];[| rewrite X'].
      { rewrite repeat_length. nia. }
      apply nth_error_in in X. apply repeat_spec in X. clarify.
      generalize Mem.setN_outside; i; unfold ZMap.get in *.
      unfold store_init_data, Mem.store in *. des_ifs; ss. 7:{ exfalso. et. }
      all: try (rewrite !PMap.gss in *; rewrite H6;[|rewrite length_inj_bytes; rewrite encode_int_length; nia]).
      all: try (rewrite H1; edestruct H0 as [x1 [X'' X''']];[| rewrite X''']; [rewrite repeat_length; nia|]).
      all: try (apply nth_error_in in X''; apply repeat_spec in X''; clarify).
      rewrite !PMap.gss in *. rewrite H6. 2:{ des_ifs. ss. nia. } rewrite H1. des_ifs.
      edestruct H0 as [x1 [X'' X''']];[| rewrite X''']; [rewrite repeat_length; nia|].
      apply nth_error_in in X''; apply repeat_spec in X''; clarify.
    + generalize Mem.setN_outside. i. unfold ZMap.get in *. rewrite H0. 2:{ rewrite repeat_length. nia. }
      destruct ((x <? z + init_data_size a) && (z <=? x))%Z eqn:?; clarify.
      * generalize setN_inside. i. unfold ZMap.get in *.
        unfold store_init_data, Mem.store in *. des_ifs; ss. 7:{ exfalso. et. }
        all: try (rewrite !PMap.gss; edestruct H6 as [x0 [X X']];[| rewrite X']; [rewrite length_inj_bytes; rewrite encode_int_length; nia|]).
        all: try (edestruct H6 as [x1 [X'' X''']];[| rewrite X''']; [rewrite length_inj_bytes; rewrite encode_int_length; nia|]; clarify).
        des_ifs. rewrite !PMap.gss. edestruct H6 as [x0 [X X']];[| rewrite X']. { ss. nia. }
        edestruct H6 as [x1 [X'' X''']];[| rewrite X''']. { ss. nia. }
        clarify.
      * unfold store_init_data, Mem.store in *. des_ifs; ss. 7:{ exfalso. et. }
        all: try (rewrite !PMap.gss; rewrite !H0; [>|rewrite length_inj_bytes; rewrite encode_int_length; nia..]).
        all: try (rewrite !H1; rewrite !H0; [>|rewrite repeat_length; nia..]; et).
        rewrite !PMap.gss; rewrite !H0; [>|des_ifs; ss; nia..].
        rewrite !H1; rewrite !H0; et. des_ifs. rewrite repeat_length; nia.
Qed.

Lemma tgt_init_mem_cnt_inbound (clight_prog: Clight.program) tm :
  Genv.init_mem clight_prog = Some tm ->
  forall b gd, Genv.find_def (Genv.globalenv clight_prog) b = Some gd ->
    match gd with
    | Gfun _ => forall ofs, (tm.(Mem.mem_contents) !! b) !! ofs = Undef
    | Gvar v => forall ofs, (tm.(Mem.mem_contents) !! b) !! ofs = (Mem.setN (Genv.bytes_of_init_data_list (Genv.globalenv clight_prog) (gvar_init v)) 0 (ZMap.init Undef)) !! ofs
    end.
Proof.
  i. unfold Genv.init_mem in H. unfold Genv.globalenv in H0. revert H H0.
  set (Genv.empty_genv _ _ _) as gi. set Mem.empty as mi.
  assert (forall b gd, Genv.find_def gi b = Some gd ->
            match gd with
            | Gfun _ => forall ofs, (mi.(Mem.mem_contents) !! b) !! ofs = Undef
            | Gvar v => forall ofs, (mi.(Mem.mem_contents) !! b) !! ofs = (Mem.setN (Genv.bytes_of_init_data_list (Genv.globalenv clight_prog) (gvar_init v)) 0 (ZMap.init Undef)) !! ofs
            end).
  { unfold gi, Genv.find_def. ss. i. rewrite PTree.gempty in H. clarify. }
  assert (Genv.genv_next gi = Mem.nextblock mi) by et. i.
  clearbody gi mi. i. revert gi mi tm H H0 b gd H2 H1. induction (AST.prog_defs clight_prog); i; ss; clarify.
  { apply H. et. }
  destruct Genv.alloc_global eqn:?; clarify. eapply IHl in H1; et; cycle 1.
  - ss. rewrite H0. clear - Heqo. unfold Genv.alloc_global in Heqo. des_ifs.
    Local Transparent Mem.alloc.
    + unfold Mem.alloc, Mem.drop_perm in *. des_ifs.
    + erewrite <- Mem.nextblock_alloc with (m1:=mi) (m2:=m0); et.
      erewrite <- Genv.store_zeros_nextblock with (m':=m1); et.
      erewrite <- Genv.store_init_data_list_nextblock with (m':=m2); et.
      unfold Mem.drop_perm in Heqo. des_ifs.
  - clear - H Heqo H0. i. unfold Genv.find_def in *.
    destruct (dec b (Genv.genv_next gi)).
    Local Opaque Mem.alloc.
    + ss. clarify. rewrite PTree.gss in H1. clarify. destruct a; ss. des_ifs.
    Local Transparent Mem.alloc.
      * unfold Mem.alloc, Mem.drop_perm in *. des_ifs. ss. rewrite H0. rewrite PMap.gss. i.
        destruct (zindex_surj ofs). clarify. pose proof ZMap.gi. unfold ZMap.get in H1. rewrite H1. et.
    Local Opaque Mem.alloc.
      * unfold Mem.drop_perm in *. des_ifs. ss. rewrite H0.
        replace (ZMap.init Undef) with (m0.(Mem.mem_contents) !! (Mem.nextblock mi)).
    Local Transparent Mem.alloc.
        2:{ unfold Mem.alloc in Heq. clarify. ss. rewrite PMap.gss. et. }
        assert (b = Mem.nextblock mi). { unfold Mem.alloc in Heq. clarify. }
        clear Heq. clarify. i. erewrite tgt_store_zero_list; et.
    + hexploit Genv.genv_defs_range; et. unfold Plt. i. ss.
      rewrite PTree.gso in H1; et.
      unfold Genv.alloc_global in Heqo. destruct a as [_ [?|?]].
      * unfold Mem.alloc, Mem.drop_perm in Heqo. des_ifs_safe. ss. rewrite H0 in n.
        rewrite !PMap.gso; et. eapply H; et.
      * des_ifs_safe. rewrite H0 in n. apply H in H1.
        replace ((Mem.mem_contents mi) !! b) with ((Mem.mem_contents m0) !! b) in H1. 2:{ unfold Mem.alloc in Heq. clarify. ss. rewrite PMap.gso; et. }
        replace ((Mem.mem_contents m) !! b) with ((Mem.mem_contents m2) !! b). 2:{ unfold Mem.drop_perm in Heqo. des_ifs. }
        assert ((Mem.mem_contents m1) !! b = (Mem.mem_contents m2) !! b).
        { clear -Heq1 n Heq. unfold Mem.alloc in Heq. clarify.
          set (gvar_init v) in Heq1. set 0%Z in Heq1. clearbody z.
          ginduction l; i; ss; clarify.
          des_ifs. change (0 + init_data_size a)%Z with (init_data_size a) in Heq1.
          eapply IHl in Heq1; et. rewrite <- Heq1. unfold Genv.store_init_data, Mem.store in Heq.
          des_ifs; ss; rewrite PMap.gso; et. }
        rewrite <- H3. assert (b0 = Mem.nextblock mi) by (unfold Mem.alloc in Heq; clarify). clarify.
        assert ((Mem.mem_contents m0) !! b = (Mem.mem_contents m1) !! b).
        { clear -Heq0 n. set (init_data_list_size _) in Heq0. set 0%Z in Heq0. clearbody z z0.
          symmetry in Heq0. apply R_store_zeros_correct in Heq0. remember (Some _) in Heq0.
          ginduction Heq0; i; ss; clarify. hexploit IHHeq0; et. i. rewrite <- H.
          unfold Mem.store in e0. des_ifs. ss. rewrite PMap.gso; et. }
        rewrite <- H4. et.
  Qed.

Lemma tgt_init_mem_cnt_outbound (clight_prog: Clight.program) tm b:
  Genv.init_mem clight_prog = Some tm ->
  (Genv.genv_next (Genv.globalenv clight_prog) <= b)%positive ->
  tm.(Mem.mem_contents) !! b = ZMap.init Undef.
Proof.
  i. unfold Genv.init_mem in H. unfold Genv.globalenv in H0. revert H H0.
  set (Genv.empty_genv _ _ _) as gi. set Mem.empty as mi.
  assert (forall b, (Genv.genv_next gi <= b)%positive ->
            mi.(Mem.mem_contents) !! b = ZMap.init Undef).
  { unfold gi. ss. i. rewrite PMap.gi. et. }
  assert (Genv.genv_next gi = Mem.nextblock mi) by et. i.
  clearbody gi mi. i. revert gi mi tm H H0 b H2 H1. induction (AST.prog_defs clight_prog); i; ss; clarify.
  { apply H. et. }
  des_ifs. eapply IHl in H1; et.
  - i. ss. rewrite H0 in *. clear -H Heq H3.
    unfold Genv.alloc_global in Heq. des_ifs. { unfold Mem.alloc, Mem.drop_perm in *. des_ifs. ss. rewrite PMap.gso; try nia. apply H. nia. }
    replace (Mem.nextblock mi) with b in *. 2:{ unfold Mem.alloc in *. clarify. }
    unfold Mem.drop_perm in Heq. des_ifs. ss.
    assert ((Mem.mem_contents m1) !! b0 = (Mem.mem_contents m2) !! b0).
    { clear - Heq2 H H3. revert Heq2. set 0%Z. set (gvar_init v). clearbody z. ginduction l; i; ss; clarify.
      des_ifs. eapply IHl in Heq2; et. rewrite <- Heq2. unfold Genv.store_init_data, Mem.store in Heq. des_ifs; ss; rewrite PMap.gso; et; nia. }
    rewrite <- H0.
    assert ((Mem.mem_contents m0) !! b0 = (Mem.mem_contents m1) !! b0).
    { clear - Heq1 H H3. symmetry in Heq1. apply R_store_zeros_correct in Heq1.
      revert Heq1. set 0%Z. clearbody z. remember (Some _). i. ginduction Heq1; i; ss; clarify.
      hexploit IHHeq1; et. i. rewrite <- H0. unfold Mem.store in e0. des_ifs. ss. rewrite PMap.gso; et. nia. }
    rewrite <- H1. unfold Mem.alloc in Heq0. clarify. ss.
    destruct (dec b0 (Mem.nextblock mi)). { clarify. rewrite PMap.gss. et. }
    rewrite PMap.gso; et. apply H. nia.
  - ss. rewrite H0. clear -Heq. unfold Genv.alloc_global in Heq. des_ifs.
    { unfold Mem.alloc, Mem.drop_perm in *. des_ifs. }
    unfold Mem.drop_perm in *. des_ifs. ss.
    replace (Mem.nextblock m2) with (Mem.nextblock m1). { erewrite Genv.store_zeros_nextblock with (m':=m1); et. unfold Mem.alloc in Heq0. clarify. }
    clear - Heq2. revert Heq2. set 0%Z. set (gvar_init v). clearbody z. ginduction l; i; ss; clarify.
    des_ifs. eapply IHl in Heq2; et. rewrite <- Heq2. unfold Genv.store_init_data, Mem.store in Heq. des_ifs.
Qed.

Lemma tgt_init_mem_access (clight_prog: Clight.program) tm :
  Genv.init_mem clight_prog = Some tm ->
  forall b gd, Genv.find_def (Genv.globalenv clight_prog) b = Some gd ->
    match gd with
    | Gfun _ => tm.(Mem.mem_access) !! b = fun ofs k => if zle 0 ofs && zlt ofs 1 then Some Nonempty else None
    | Gvar v => tm.(Mem.mem_access) !! b = fun ofs k => if zle 0 ofs && zlt ofs (init_data_list_size (gvar_init v)) then Some (Genv.perm_globvar v) else None
    end.
Proof.
  i. unfold Genv.init_mem in H. unfold Genv.globalenv in H0. revert H H0.
  set (Genv.empty_genv _ _ _) as gi. set Mem.empty as mi.
  assert (forall b gd, Genv.find_def gi b = Some gd ->
            match gd with
            | Gfun _ => mi.(Mem.mem_access) !! b = fun ofs k => if zle 0 ofs && zlt ofs 1 then Some Nonempty else None
            | Gvar v => mi.(Mem.mem_access) !! b = fun ofs k => if zle 0 ofs && zlt ofs (init_data_list_size (gvar_init v)) then Some (Genv.perm_globvar v) else None
            end).
  { unfold gi, Genv.find_def. ss. i. rewrite PTree.gempty in H. clarify. }
  assert (Genv.genv_next gi = Mem.nextblock mi) by et. i.
  clearbody gi mi. i. revert gi mi tm H H0 b gd H2 H1. induction (AST.prog_defs clight_prog); i; ss; clarify.
  { apply H. et. }
  destruct Genv.alloc_global eqn:?; clarify. eapply IHl in H1; et; cycle 1.
  - ss. rewrite H0. clear - Heqo. unfold Genv.alloc_global in Heqo. des_ifs.
    Local Transparent Mem.alloc.
    + unfold Mem.alloc, Mem.drop_perm in *. des_ifs.
    + erewrite <- Mem.nextblock_alloc with (m1:=mi) (m2:=m0); et.
      erewrite <- Genv.store_zeros_nextblock with (m':=m1); et.
      erewrite <- Genv.store_init_data_list_nextblock with (m':=m2); et.
      unfold Mem.drop_perm in Heqo. des_ifs.
  - clear - H Heqo H0. i. unfold Genv.find_def in *. ss. rewrite H0 in *.
    destruct (dec b (Mem.nextblock mi)).
    Local Opaque Mem.alloc.
    + clarify. rewrite PTree.gss in H1. clarify. destruct a; ss. des_ifs.
    Local Transparent Mem.alloc.
      * unfold Mem.alloc, Mem.drop_perm in *. des_ifs. ss. rewrite !PMap.gss. extensionalities. des_ifs.
      * unfold Mem.drop_perm in *. des_ifs. ss.
        assert (b = Mem.nextblock mi). { unfold Mem.alloc in Heq. clarify. }
        clarify. rewrite PMap.gss. extensionalities. des_ifs.
        assert ((Mem.mem_access m2) !! (Mem.nextblock mi) = (Mem.mem_access m1) !! (Mem.nextblock mi)).
        { clear -Heq1. set (gvar_init v) in Heq1. set 0%Z in Heq1. clearbody z.
          ginduction l; i; ss; clarify.
          des_ifs. change (0 + init_data_size a)%Z with (init_data_size a) in Heq1.
          eapply IHl in Heq1; et. rewrite Heq1. unfold Genv.store_init_data, Mem.store in Heq.
          des_ifs; ss; rewrite PMap.gss. }
        rewrite H3.
        assert ((Mem.mem_access m1) !! (Mem.nextblock mi) = (Mem.mem_access m0) !! (Mem.nextblock mi)).
        { clear - Heq0. symmetry in Heq0. apply R_store_zeros_correct in Heq0. revert Heq0. set 0%Z. remember (Some _).
          i. clearbody z. ginduction Heq0; i; ss; clarify. hexploit IHHeq0; et. i. rewrite H. unfold Mem.store in e0. des_ifs. }
        rewrite H4. unfold Mem.alloc in Heq. clarify. ss. rewrite PMap.gss.
        rewrite Heq2. et.
    + rewrite PTree.gso in H1; et.
      unfold Genv.alloc_global in Heqo. destruct a as [_ [?|?]].
      * unfold Mem.alloc, Mem.drop_perm in Heqo. des_ifs_safe. ss. rewrite !PMap.gso; et. eapply H; et.
      * des_ifs_safe. apply H in H1.
        replace ((Mem.mem_access mi) !! b) with ((Mem.mem_access m0) !! b) in H1. 2:{ unfold Mem.alloc in Heq. clarify. ss. rewrite PMap.gso; et. }
        replace ((Mem.mem_access m) !! b) with ((Mem.mem_access m2) !! b). 2:{ clear H1. unfold Mem.drop_perm in Heqo. des_ifs. ss. rewrite PMap.gso; et. unfold Mem.alloc in Heq. clarify. }
        assert ((Mem.mem_access m1) !! b = (Mem.mem_access m2) !! b).
        { clear -Heq1 n Heq. unfold Mem.alloc in Heq. clarify.
          set (gvar_init v) in Heq1. set 0%Z in Heq1. clearbody z.
          ginduction l; i; ss; clarify.
          des_ifs. change (0 + init_data_size a)%Z with (init_data_size a) in Heq1.
          eapply IHl in Heq1; et. rewrite <- Heq1. unfold Genv.store_init_data, Mem.store in Heq.
          des_ifs; ss; rewrite PMap.gso; et. }
        rewrite <- H2. assert (b0 = Mem.nextblock mi) by (unfold Mem.alloc in Heq; clarify). clarify.
        assert ((Mem.mem_access m0) !! b = (Mem.mem_access m1) !! b).
        { clear -Heq0 n. set (init_data_list_size _) in Heq0. set 0%Z in Heq0. clearbody z z0.
          symmetry in Heq0. apply R_store_zeros_correct in Heq0. remember (Some _) in Heq0.
          ginduction Heq0; i; ss; clarify. hexploit IHHeq0; et. i. rewrite <- H.
          unfold Mem.store in e0. des_ifs. }
        rewrite <- H3. et.
Qed.

(* tgt_init_mem_nextblock = Genv.init_mem_genv_next *)
(* tgt_init_mem_concrete = Genv.init_mem_logical *)

Lemma src_alloc_global_cnt_invariant sk ski m m0 b:
  alloc_globals sk m0 ski = Some m ->
    (b < m0.(Mem.nextblock))%positive ->
      m.(Mem.mem_contents) !! b = m0.(Mem.mem_contents) !! b.
Proof.
  ginduction ski; i; ss; clarify. des_ifs.
  eapply IHski with (b:=b) in H.
  - rewrite H. clear -Heq H0. unfold alloc_global in Heq. des_ifs. { unfold Mem.alloc, Mem.drop_perm in *. des_ifs. ss. rewrite PMap.gso; et. nia. }
    replace (Mem.mem_contents m1) with (Mem.mem_contents m3) by (unfold Mem.drop_perm in Heq; des_ifs; ss).
    replace (Mem.nextblock m0) with b0 in * by (unfold Mem.alloc in *; clarify).
    assert ((Mem.mem_contents m) !! b = (Mem.mem_contents m2) !! b).
    { clear -Heq1 H0. symmetry in Heq1. apply R_store_zeros_correct in Heq1. remember (Some _) in Heq1.
      ginduction Heq1; i; ss; clarify. hexploit IHHeq1; et. i. rewrite <- H.
      unfold Mem.store in e0. des_ifs. ss. rewrite PMap.gso; et. nia. }
    assert ((Mem.mem_contents m2) !! b = (Mem.mem_contents m3) !! b).
    { clear -Heq2 H0. set 0%Z in Heq2. clearbody z. set (gvar_init v) in Heq2.
      ginduction l; i; ss; clarify. des_ifs. eapply IHl in Heq2; et.
      unfold store_init_data, Mem.store in Heq. des_ifs; ss; rewrite PMap.gso in *; et; nia. }
    rewrite <- H1. rewrite <- H. unfold Mem.alloc in Heq0. des_ifs. ss. rewrite PMap.gso; et. nia.
  - etrans; et. unfold alloc_global in Heq. des_ifs. { unfold Mem.alloc, Mem.drop_perm in *. des_ifs. ss. nia. }
    replace (Mem.nextblock m1) with (Mem.nextblock m4) by (unfold Mem.drop_perm in Heq; des_ifs; ss).
    assert (Pos.succ (Mem.nextblock m0) = Mem.nextblock m2) by (unfold Mem.alloc in Heq0; des_ifs; ss).
    erewrite <- Genv.store_zeros_nextblock with (m:=m2) in H1; et.
    replace (Mem.nextblock m4) with (Mem.nextblock m3); try nia.
    clear - Heq2. set 0%Z in Heq2. set (gvar_init v) in *. clearbody z. ginduction l; i; ss; clarify.
    des_ifs. eapply IHl in Heq2. rewrite <- Heq2. clear -Heq. unfold store_init_data, Mem.store in Heq. des_ifs.
Qed.

Lemma src_alloc_global_access_invariant sk ski m m0 b:
  alloc_globals sk m0 ski = Some m ->
    (b < m0.(Mem.nextblock))%positive ->
      m.(Mem.mem_access) !! b = m0.(Mem.mem_access) !! b.
Proof.
  ginduction ski; i; ss; clarify. des_ifs.
  eapply IHski with (b:=b) in H.
  - rewrite H. clear -Heq H0. unfold alloc_global in Heq. des_ifs. { unfold Mem.alloc, Mem.drop_perm in *. des_ifs. ss. rewrite !PMap.gss. rewrite !PMap.gso; et; try nia. }
    replace ((Mem.mem_access m1) !! b) with ((Mem.mem_access m3) !! b).
    2:{ unfold Mem.drop_perm in Heq; des_ifs; ss. rewrite PMap.gso; et. unfold Mem.alloc in Heq0. clarify. nia. }
    replace (Mem.nextblock m0) with b0 in * by (unfold Mem.alloc in *; clarify).
    assert ((Mem.mem_access m) !! b = (Mem.mem_access m2) !! b).
    { clear -Heq1 H0. symmetry in Heq1. apply R_store_zeros_correct in Heq1. remember (Some _) in Heq1.
      ginduction Heq1; i; ss; clarify. hexploit IHHeq1; et. i. rewrite <- H.
      unfold Mem.store in e0. des_ifs. }
    assert ((Mem.mem_access m2) !! b = (Mem.mem_access m3) !! b).
    { clear -Heq2 H0. set 0%Z in Heq2. clearbody z. set (gvar_init v) in Heq2.
      ginduction l; i; ss; clarify. des_ifs. eapply IHl in Heq2; et.
      unfold store_init_data, Mem.store in Heq. des_ifs; ss; rewrite PMap.gso in *; et; nia. }
    rewrite <- H1. rewrite <- H. unfold Mem.alloc in Heq0. des_ifs. ss. rewrite PMap.gso; et. nia.
  - etrans; et. unfold alloc_global in Heq. des_ifs. { unfold Mem.alloc, Mem.drop_perm in *. des_ifs. ss. nia. }
    replace (Mem.nextblock m1) with (Mem.nextblock m4) by (unfold Mem.drop_perm in Heq; des_ifs; ss).
    assert (Pos.succ (Mem.nextblock m0) = Mem.nextblock m2) by (unfold Mem.alloc in Heq0; des_ifs; ss).
    erewrite <- Genv.store_zeros_nextblock with (m:=m2) in H1; et.
    replace (Mem.nextblock m4) with (Mem.nextblock m3); try nia.
    clear - Heq2. set 0%Z in Heq2. set (gvar_init v) in *. clearbody z. ginduction l; i; ss; clarify.
    des_ifs. eapply IHl in Heq2. rewrite <- Heq2. clear -Heq. unfold store_init_data, Mem.store in Heq. des_ifs.
Qed.

Lemma src_init_mem_cnt_inbound sk m :
  load_mem sk = Some m ->
  forall idx s gd, nth_error sk idx = Some (s, gd) ->
    match gd with
    | Gfun _ => forall ofs, (m.(Mem.mem_contents) !! (Pos.of_succ_nat idx)) !! ofs = Undef
    | Gvar v => forall ofs, (m.(Mem.mem_contents) !! (Pos.of_succ_nat idx)) !! ofs = (Mem.setN (bytes_of_init_data_list sk (gvar_init v)) 0 (ZMap.init Undef)) !! ofs
    end.
Proof.
  i. unfold load_mem in H. revert H H0.
  set sk as ski at 2 3. set Mem.empty as mi.
  replace (Pos.of_succ_nat idx) with (Pos.of_nat ((Pos.to_nat (Mem.nextblock mi)) + idx)) by (ss; nia).
  clearbody ski mi. i. revert ski mi m gd s idx H H0.
  induction ski; i; ss; clarify.
  { destruct idx; ss. }
  des_ifs_safe. destruct idx; ss; clarify; cycle 1.
  { eapply IHski in H; et. replace (Pos.to_nat (Mem.nextblock mi) + S idx) with (Pos.to_nat (Mem.nextblock m0) + idx); et.
    clear - Heq. unfold alloc_global in Heq. des_ifs; [unfold Mem.alloc, Mem.drop_perm in *|]; des_ifs; ss; try nia.
    unfold Mem.drop_perm in Heq. des_ifs. ss.
    replace (Mem.nextblock m2) with (Mem.nextblock m1). { erewrite Genv.store_zeros_nextblock; et. unfold Mem.alloc in *. clarify. ss. nia. }
    clear - Heq2. revert Heq2. set 0%Z. set (gvar_init v). clearbody z. ginduction l; i; ss; clarify; try nia.
    des_ifs. apply IHl in Heq2. rewrite <- Heq2. unfold store_init_data, Mem.store in Heq. des_ifs. }
  clear - IHski Heq H. unfold alloc_global in Heq. des_ifs.
  - i. erewrite src_alloc_global_cnt_invariant; et; cycle 1.
    { unfold Mem.alloc, Mem.drop_perm in *. des_ifs. ss. nia. }
    unfold Mem.alloc, Mem.drop_perm in *. des_ifs. ss.
    rewrite Nat.add_0_r. rewrite Pos2Nat.id. rewrite PMap.gss. rewrite PMap.gi. et.
  - i. erewrite src_alloc_global_cnt_invariant; et; cycle 1.
    { replace (Mem.nextblock m0) with (Mem.nextblock m1). { unfold Mem.alloc in Heq0. clarify. ss. nia. }
      erewrite <- Genv.store_zeros_nextblock with (m:=m1);[|et].
      replace (Mem.nextblock m0) with (Mem.nextblock m3). 2:{ unfold Mem.drop_perm in Heq. des_ifs. }
      revert Heq2. clear. set 0%Z. set (gvar_init v). clearbody z. ginduction l; i; ss; clarify. des_ifs.
      hexploit IHl; et. i. rewrite <- H. unfold store_init_data, Mem.store in Heq. des_ifs. }
    clear H. unfold Mem.drop_perm in Heq. des_ifs. ss. replace b with (Mem.nextblock mi) in * by (unfold Mem.alloc in Heq0; clarify).
    replace (Pos.of_nat _) with (Mem.nextblock mi) by nia. erewrite src_store_zero_list; et.
    do 2 f_equal. unfold Mem.alloc in Heq0. clarify. ss. rewrite PMap.gss. et.
Qed.

Lemma src_init_mem_cnt_outbound sk m b:
  load_mem sk = Some m ->
    (Pos.of_succ_nat (List.length sk) <= b)%positive ->
      m.(Mem.mem_contents) !! b = ZMap.init Undef.
Proof.
  i. unfold load_mem in H. revert H H0.
  set sk as ski at 2 3. set Mem.empty as mi.
  replace (Pos.of_succ_nat (List.length ski)) with (Pos.of_nat ((Pos.to_nat (Mem.nextblock mi)) + (List.length ski))) by (ss; nia).
  assert (forall b, (mi.(Mem.nextblock) <= b)%positive -> mi.(Mem.mem_contents) !! b = ZMap.init Undef).
  { i. ss. rewrite PMap.gi. et. }
  clearbody ski mi. i. revert ski mi m b H H0 H1.
  induction ski; i; ss; clarify. { apply H. nia. }
  des_ifs_safe. hexploit IHski. 2:et. all: et.
  - i. clear -H Heq H2. unfold alloc_global in Heq. des_ifs.
    { unfold Mem.alloc, Mem.drop_perm in *. des_ifs. ss. rewrite PMap.gso; try nia. apply H. nia. }
    replace (Mem.nextblock m0) with (Pos.succ b) in *.
    2:{ clear H2. unfold Mem.drop_perm in *. des_ifs. ss.
        replace (Mem.nextblock m2) with (Mem.nextblock m1). { erewrite Genv.store_zeros_nextblock; et. unfold Mem.alloc in Heq0. clarify. }
        clear - Heq2. revert Heq2. set 0%Z. set (gvar_init v). clearbody z. ginduction l; i; ss; clarify.
        des_ifs. eapply IHl in Heq2; et. rewrite <- Heq2. unfold store_init_data, Mem.store in Heq. des_ifs. }
    unfold Mem.drop_perm in Heq. des_ifs. ss.
    assert ((Mem.mem_contents m1) !! b0 = (Mem.mem_contents m2) !! b0).
    { clear - Heq2 H2. revert Heq2. set 0%Z. set (gvar_init v). clearbody z. ginduction l; i; ss; clarify.
      des_ifs. eapply IHl in Heq2; et. rewrite <- Heq2. unfold store_init_data, Mem.store in Heq. des_ifs; ss; rewrite PMap.gso; et; nia. }
    rewrite <- H0.
    assert ((Mem.mem_contents m) !! b0 = (Mem.mem_contents m1) !! b0).
    { clear - Heq1 H2. symmetry in Heq1. apply R_store_zeros_correct in Heq1.
      revert Heq1. set 0%Z. clearbody z. remember (Some _). i. ginduction Heq1; i; ss; clarify.
      hexploit IHHeq1; et. i. rewrite <- H. unfold Mem.store in e0. des_ifs. ss. rewrite PMap.gso; et. nia. }
    rewrite <- H1. unfold Mem.alloc in Heq0. clarify. ss.
    destruct (dec b0 (Mem.nextblock mi)). { clarify. rewrite PMap.gss. et. }
    rewrite PMap.gso; et. apply H. nia.
  - i. clear -Heq H1. unfold alloc_global in Heq. des_ifs.
    { unfold Mem.alloc, Mem.drop_perm in *. des_ifs. ss. nia. }
    unfold Mem.drop_perm in *. des_ifs. ss.
    replace (Mem.nextblock m2) with (Mem.nextblock m1). { erewrite Genv.store_zeros_nextblock; et. unfold Mem.alloc in Heq0. clarify. ss. nia. }
    clear - Heq2. revert Heq2. set 0%Z. set (gvar_init v). clearbody z. ginduction l; i; ss; clarify.
    des_ifs. eapply IHl in Heq2; et. rewrite <- Heq2. unfold store_init_data, Mem.store in Heq. des_ifs.
Qed.

Lemma src_init_mem_access (sk: Sk.t) m :
  load_mem sk = Some m ->
  forall idx s gd, nth_error sk idx = Some (s, gd) ->
    match gd with
    | Gfun _ => m.(Mem.mem_access) !! (Pos.of_succ_nat idx) = fun ofs k => if zle 0 ofs && zlt ofs 1 then Some Nonempty else None
    | Gvar v => m.(Mem.mem_access) !! (Pos.of_succ_nat idx) = fun ofs k => if zle 0 ofs && zlt ofs (init_data_list_size (gvar_init v)) then Some (Genv.perm_globvar v) else None
    end.
Proof.
  i. unfold load_mem in H. revert H H0.
  set sk as ski at 2 3. set Mem.empty as mi.
  replace (Pos.of_succ_nat idx) with (Pos.of_nat ((Pos.to_nat (Mem.nextblock mi)) + idx)) by (ss; nia).
  clearbody ski mi. i. revert ski mi m gd s idx H H0.
  induction ski; i; ss; clarify.
  { destruct idx; ss. }
  des_ifs_safe. destruct idx; ss; clarify; cycle 1.
  { eapply IHski in H; et. replace (Pos.to_nat (Mem.nextblock mi) + S idx) with (Pos.to_nat (Mem.nextblock m0) + idx); et.
    clear - Heq. unfold alloc_global in Heq. des_ifs; [unfold Mem.alloc, Mem.drop_perm in *|]; des_ifs; ss; try nia.
    unfold Mem.drop_perm in Heq. des_ifs. ss.
    replace (Mem.nextblock m2) with (Mem.nextblock m1). { erewrite Genv.store_zeros_nextblock; et. unfold Mem.alloc in *. clarify. ss. nia. }
    clear - Heq2. revert Heq2. set 0%Z. set (gvar_init v). clearbody z. ginduction l; i; ss; clarify; try nia.
    des_ifs. apply IHl in Heq2. rewrite <- Heq2. unfold store_init_data, Mem.store in Heq. des_ifs. }
  clear - IHski Heq H. unfold alloc_global in Heq. des_ifs.
  - erewrite src_alloc_global_access_invariant; et; cycle 1.
    { unfold Mem.alloc, Mem.drop_perm in *. des_ifs. ss. nia. }
    unfold Mem.alloc, Mem.drop_perm in *. des_ifs. ss.
    rewrite Nat.add_0_r. rewrite Pos2Nat.id. rewrite PMap.gss.
    extensionalities. des_ifs. rewrite PMap.gss. des_ifs.
  - i. erewrite src_alloc_global_access_invariant; et; cycle 1.
    { replace (Mem.nextblock m0) with (Mem.nextblock m1). { unfold Mem.alloc in Heq0. clarify. ss. nia. }
      erewrite <- Genv.store_zeros_nextblock with (m:=m1);[|et].
      replace (Mem.nextblock m0) with (Mem.nextblock m3). 2:{ unfold Mem.drop_perm in Heq. des_ifs. }
      revert Heq2. clear. set 0%Z. set (gvar_init v). clearbody z. ginduction l; i; ss; clarify. des_ifs.
      hexploit IHl; et. i. rewrite <- H. unfold store_init_data, Mem.store in Heq. des_ifs. }
    clear H. unfold Mem.drop_perm in Heq. des_ifs. ss. replace b with (Mem.nextblock mi) in * by (unfold Mem.alloc in Heq0; clarify).
    replace (Pos.of_nat _) with (Mem.nextblock mi) by nia.
    rewrite PMap.gss. extensionalities. des_ifs.
    assert ((Mem.mem_access m2) !! (Mem.nextblock mi) = (Mem.mem_access m3) !! (Mem.nextblock mi)).
    { clear -Heq2 H0. set 0%Z in Heq2. clearbody z. set (gvar_init v) in Heq2.
      ginduction l; i; ss; clarify. des_ifs. eapply IHl in Heq2; et.
      unfold store_init_data, Mem.store in Heq. des_ifs; ss; rewrite PMap.gso in *; et; nia. }
    assert ((Mem.mem_access m1) !! (Mem.nextblock mi) = (Mem.mem_access m2) !! (Mem.nextblock mi)).
    { clear -Heq1 H0. symmetry in Heq1. apply R_store_zeros_correct in Heq1. remember (Some _) in Heq1.
      ginduction Heq1; i; ss; clarify. hexploit IHHeq1; et. i. rewrite <- H.
      unfold Mem.store in e0. des_ifs. }
    rewrite <- H1. rewrite <- H2. unfold Mem.alloc in Heq0. des_ifs. ss. rewrite PMap.gss. des_ifs.
Qed.

Lemma src_init_mem_nextblock sk m :
  load_mem sk = Some m -> Pos.of_succ_nat (List.length sk) = Mem.nextblock m.
Proof.
  unfold load_mem. generalize sk at 1.
  replace (Pos.of_succ_nat _) with (Pos.of_nat (Pos.to_nat (Mem.nextblock Mem.empty) + List.length sk)) by (ss; nia).
  generalize Mem.empty. intros mi sk'. revert mi m. induction sk; i; ss; clarify; try nia.
  des_ifs. erewrite <- IHsk with (m:=m); et.
  replace (Mem.nextblock m0) with (Pos.succ (Mem.nextblock mi)); try nia.
  clear -Heq. unfold alloc_global in Heq. des_ifs.
  - replace (Mem.nextblock m0) with (Mem.nextblock m) by (unfold Mem.drop_perm in Heq; des_ifs).
    Local Transparent Mem.alloc.
    unfold Mem.alloc in Heq0. clarify.
  - replace (Mem.nextblock m0) with (Mem.nextblock m2) by (unfold Mem.drop_perm in Heq; des_ifs).
    replace (Pos.succ (Mem.nextblock mi)) with (Mem.nextblock m) by (unfold Mem.alloc in Heq0; clarify).
    erewrite <- Genv.store_zeros_nextblock with (m':=m1); et.
    clear -Heq2. revert Heq2. generalize 0%Z. revert b m1 m2.
    induction (gvar_init v); i; ss; clarify.
    des_ifs. apply IHl in Heq2. rewrite <- Heq2. unfold store_init_data, Mem.store in Heq.
    des_ifs.
Qed.

Lemma src_init_mem_concrete sk m b :
  load_mem sk = Some m -> m.(Mem.mem_concrete) ! b = None.
Proof.
  i. revert b.
  assert (forall b, (Mem.mem_concrete Mem.empty) ! b = None).
  { i. ss. rewrite PTree.gempty. et. }
  revert m H H0. unfold load_mem. generalize sk at 1.
  generalize Mem.empty. intros mi sk'. revert mi.
  induction sk; i; ss; clarify; try nia.
  des_ifs. erewrite <- IHsk with (m:=m); et.
  clear -Heq H0. unfold alloc_global in Heq. des_ifs.
  - unfold Mem.alloc, Mem.drop_perm in *. des_ifs.
  - replace (Mem.mem_concrete m0) with (Mem.mem_concrete m2) by (unfold Mem.drop_perm in Heq; des_ifs).
    replace (Mem.mem_concrete mi) with (Mem.mem_concrete m) in H0 by (unfold Mem.alloc in Heq0; clarify).
    erewrite Genv.concrete_store_zeros in H0; [|et].
    clear -Heq2 H0. revert Heq2. generalize 0%Z. revert m1 m2 H0.
    induction (gvar_init v); i; ss; clarify.
    des_ifs. eapply IHl in Heq2; et.
    unfold store_init_data, Mem.store in Heq.
    des_ifs.
Qed.

Lemma match_mem_init_success sk clight_prog m:
  load_mem sk = Some m ->
  match_ge sk (globalenv clight_prog)->
  (forall id v, In (id, Gvar v) (prog_defs clight_prog) -> In (string_of_ident id, Gvar v) sk) ->
  (forall id v, In (id, Gvar v) (prog_defs clight_prog) -> forall symb ofs, In (Init_addrof symb ofs) (gvar_init v) -> chk_ident symb = true) ->
  exists tm, Genv.init_mem clight_prog = Some tm.
Proof.
  i. apply Genv.init_mem_exists. i.
  eapply load_mem_inversion in H; et.
  des. split; et. i. hexploit H4; et. i. des. inv H0. apply MGE in H6.
  hexploit H2; et. i. unfold chk_ident in H0. destruct Pos.eq_dec; clarify. rewrite e. et.
Qed.

Theorem compile_init_mem_success clight_prog mn md sk_mem:
  compile clight_prog mn = OK md ->
  mem_skel clight_prog = OK sk_mem ->
  exists m tm,
  load_mem (Sk.canon (Sk.add sk_mem (Mod.sk md))) = Some m
  /\ Genv.init_mem clight_prog = Some tm
  /\ match_mem (Sk.canon (Sk.add sk_mem (Mod.sk md))) (globalenv clight_prog) m tm.
Proof.
  i. hexploit compile_match_genv; et. i. unfold compile, mem_skel in *. des_ifs.
  ss. dup m. rename m0 into X. apply load_mem_exists in m. des. rewrite m. revert H1 m. set (List.map _ _) as sk_mem. i.
  assert (exists tm, Genv.init_mem clight_prog = Some tm /\
          match_mem (sort (Sk.add sk_mem t)) (Genv.globalenv clight_prog) m0 tm); [|des;et].
  clear - Heq H1 m X.
  assert (exists tm, Genv.init_mem clight_prog = Some tm).
  { eapply match_mem_init_success; et.
    - clear - Heq. unfold get_sk in Heq. des_ifs. i. generalize Sk.le_canon. i. ss. apply H0.
      unfold Sk.add. ss. rewrite in_app. right. rewrite in_map_iff. exists (id, Gvar v).
      split; et. apply filter_In. et.
    - clear - Heq. unfold get_sk in Heq. des_ifs. i. bsimpl. des.
      rewrite forallb_forall in Heq2. hexploit (Heq2 (Gvar v)); cycle 1.
      { i. ss. des_ifs. ss. rewrite forallb_forall in H1. hexploit H1; et. }
      rewrite in_map_iff. exists (id, Gvar v). split; et. apply filter_In. et. }
  des. assert (match_mem (sort (Sk.add sk_mem t)) (Genv.globalenv clight_prog) m0 tm); et.
  econs.
  - erewrite src_init_mem_nextblock; et. nia.
  - hexploit src_init_mem_nextblock; et. i. rewrite <- H0. unfold map_blk. des_ifs; try nia.
    rewrite Zplus_minus in Heq0. clarify. erewrite Genv.init_mem_genv_next; et.
  - i. assert (exists idx, Pos.of_succ_nat idx = b).
    { assert (0 < Pos.to_nat b) by nia.
      assert (exists n, Pos.to_nat b = S n). { destruct (Pos.to_nat b); try nia. et. }
      des. eexists. erewrite SuccNat2Pos.inv; et. }
    des. clarify. change (list _) with Sk.t in sk_mem.
    destruct (dec_le (List.length (sort (Sk.add sk_mem t))) idx).
    + erewrite src_init_mem_cnt_outbound with (m:=m0); et; try nia.
      erewrite tgt_init_mem_cnt_outbound; et.
      2:{ apply map_blk_local_region. nia. }
      rewrite !PMap.gi. ss.
    + edestruct (nth_error_Some (sort (Sk.add sk_mem t)) idx). hexploit H3; try nia.
      i. destruct nth_error eqn:?; clarify. destruct p.
      eapply src_init_mem_cnt_inbound in m; et.
      inv H1. hexploit ELEM; et. i.
      eapply tgt_init_mem_cnt_inbound in H; et.
      des_ifs. { rewrite m. rewrite H. ss. }
      rewrite m. rewrite H. destruct (zindex_surj ofs). clarify.
      set (Mem.setN _ _ _). change (t0 !! (ZIndexed.index x)) with (ZMap.get x t0).
      set (Mem.setN _ _ _). change (t1 !! (ZIndexed.index x)) with (ZMap.get x t1).
      unfold t0, t1.
      destruct ((x <? 0) || (x >=? 0 + init_data_list_size (gvar_init v)))%Z eqn: e1.
      * rewrite Mem.setN_outside. { rewrite Mem.setN_outside. { unfold ZMap.get. rewrite PMap.gi. ss. } rewrite src_bytes_of_init_data_list_len. nia. }
        rewrite tgt_bytes_of_init_data_list_len. nia.
      * set (Genv.bytes_of_init_data_list _ _). set (bytes_of_init_data_list _ _).
        hexploit (@setN_inside x l 0). { unfold l. rewrite tgt_bytes_of_init_data_list_len. nia. }
        hexploit (@setN_inside x l0 0). { unfold l0. rewrite src_bytes_of_init_data_list_len. nia. }
        i. des. rewrite H8. rewrite H7. generalize match_bytes_of_gvar_init.
        i. apply nth_error_in in Heqo. hexploit H9; et.
        { unfold mem_skel. des_ifs. } { econs; et. }
        i. clear - H5 H6 H10. unfold l0, l in *. unfold fundef in H10. rewrite <- H10 in H6.
        rewrite list_map_nth in H6. unfold option_map in H6. des_ifs.
        f_equal. ss. rewrite H5 in Heq. clarify.
  - i. assert (exists idx, Pos.of_succ_nat idx = b).
    { assert (0 < Pos.to_nat b) by nia.
      assert (exists n, Pos.to_nat b = S n). { destruct (Pos.to_nat b); try nia. et. }
      des. eexists. erewrite SuccNat2Pos.inv; et. }
    des. clarify. change (list _) with Sk.t in sk_mem.
    destruct (dec_le (List.length (sort (Sk.add sk_mem t))) idx).
    + extensionalities. rewrite m0.(Mem.nextblock_noaccess).
      2:{ erewrite <- src_init_mem_nextblock; et. unfold Plt. nia. }
      rewrite tm.(Mem.nextblock_noaccess); et.
      unfold Plt. erewrite <- Genv.init_mem_genv_next; et.
      unfold map_blk. des_ifs; try nia.
      ii. unfold fundef in *. nia.
    + edestruct (nth_error_Some (sort (Sk.add sk_mem t)) idx). hexploit H3; try nia.
      i. destruct nth_error eqn:?; clarify. destruct p.
      eapply src_init_mem_access in m; et.
      inv H1. apply ELEM in Heqo.
      eapply tgt_init_mem_access in H; et.
      des_ifs; rewrite m; rewrite H; et.
  - i. erewrite Genv.init_mem_logical with (m:=tm); et.
    erewrite src_init_mem_concrete; et.
Qed.