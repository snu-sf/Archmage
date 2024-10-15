From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory.
Require Import CoqlibCCR.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import IRed.
Require Import ClightPlusExprgen.
Require Import STS2SmallStep.
Require Import ClightPlusMem0.

Require Import ClightPlusMatchEnv.
Require Import ClightPlusLenvSim.
Require Import ClightPlusMemSim.

From compcert Require Import Values Ctypes Clight Clightdefs.

Section PROOF.

  Import ModSemL.

  Let _sim_mon := Eval simpl in (fun (src: ModL.t) (tgt: Clight.program) => @sim_mon (ModL.compile src) (semantics3 tgt)).
  Hint Resolve _sim_mon: paco.

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); try pfold; econs 3; ss; clarify; eexists; exists (step_tau _).

  Ltac solve_ub := des; irw in H; dependent destruction H; clarify.
  Ltac sim_triggerUB :=
    (try rename H into HH); ss; unfold triggerUB; try sim_red; try pfold; econs 5; i; ss; auto;
                        [solve_ub | irw in  STEP; dependent destruction STEP; clarify].

  Ltac remove_UBcase := des_ifs; try sim_red; try solve [sim_triggerUB].

  Ltac step := repeat (sim_red; try sim_tau).

  Ltac eapplyf NEXT := let X := fresh "X" in hexploit NEXT;[..|intro X; punfold X; et].

  Local Opaque Pos.of_nat.

  Local Opaque Pos.of_succ_nat.

  Lemma step_load pstate f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    chunk addr
    tf tcode tcont ktr b r mn
    (NEXT: forall v,
            Mem.loadv chunk tm (map_val sk tge addr) = Some (map_val sk tge v) ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              (ktr (pstate, v))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: p_state * val <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (ccallU "load" (chunk, addr)))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold ccallU. sim_red.
    sim_tau. ss. sim_red. unfold loadF. repeat (sim_red; sim_tau). sim_red.
    rewrite PSTATE. sim_red. unfold unwrapU. remove_UBcase. sim_tau. sim_red. rewrite Any.upcast_downcast.
    sim_red. eapplyf NEXT. unfold Mem.loadv in *. des_ifs_safe.
    destruct addr; ss; cycle 1.
    - clarify. hexploit match_mem_load; et.
    - destruct Archi.ptr64 eqn:?; clarify.
      destruct Int64.eq eqn:?; clarify.
      destruct Mem.denormalize eqn:? in Heq0; clarify.
      destruct p. clarify. hexploit match_mem_denormalize; et.
      i. rewrite H. hexploit match_mem_load; et.
  Qed.

  Lemma step_store pstate f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    chunk addr v
    tf tcode tcont ktr b r mn
    (NEXT: forall tm' m',
            Mem.storev chunk tm (map_val sk tge addr) (map_val sk tge v) = Some tm' ->
            match_mem sk tge m' tm' ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, ()))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: p_state * () <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (ccallU "store" (chunk, addr, v)))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold ccallU. sim_red. sim_tau. ss. sim_red. unfold storeF. sim_red. repeat (sim_tau; sim_red).
    rewrite PSTATE. sim_red. unfold unwrapU. remove_UBcase. repeat (sim_tau; sim_red). rewrite Any.upcast_downcast.
    sim_red. unfold Mem.storev in Heq. des_ifs.
    - hexploit match_mem_denormalize; et. i.
      hexploit match_mem_store; et. i. des. eapplyf NEXT; et.
      unfold Mem.storev. ss. des_ifs.
    - hexploit match_mem_store; et. i. des. eapplyf NEXT; et.
  Qed.

  Lemma step_memcpy pstate f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    al sz vp v
    tf tcode tcont ktr b r mn
    (NEXT: forall tm' m',
            extcall_memcpy_sem sz al tge [map_val sk tge vp; map_val sk tge v] tm E0 Vundef tm' ->
            match_mem sk tge m' tm' ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, Vundef))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: p_state * val <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (ccallU "memcpy" (al, sz, [vp; v])))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold ccallU. sim_red. sim_tau. ss. sim_red. destruct dec.
    - sim_red. sim_tau. sim_red. hexploit NEXT; et. { econs 2. et. }
      i. punfold H. assert (update pstate "Mem" m↑ = pstate).
      { extensionalities. unfold update. destruct dec; et. subst. et. }
      rewrite H0 in H. et.
    - repeat (sim_red; sim_tau). sim_red. rewrite PSTATE.
      rewrite Any.upcast_downcast. sim_red.
      unfold unwrapU. remove_UBcase. remove_UBcase. remove_UBcase.
      repeat ((repeat sim_red); sim_tau). sim_red.
      rewrite Any.upcast_downcast. sim_red.
      hexploit match_to_ptr; et. i. move Heq at bottom.
      hexploit match_to_ptr; et. i. ss.
      hexploit match_mem_loadbytes; et. i.
      hexploit match_mem_storebytes; et. i. des.
      eapplyf NEXT; et.
      bsimpl. repeat destruct Zdivide_dec; ss; try nia.
      repeat destruct Coqlib.zle; ss; try nia.
      repeat destruct dec; ss; try nia.
      all: econs; et; try nia.
      + repeat destruct dec; ss; et; des; clarify.
      + repeat destruct dec; ss; et; des; clarify.
      + destruct (dec (Ptrofs.unsigned _) _) in Heq2; et.
        left. ss. destruct (dec b1 b0); ss; des; clarify.
        all: ii; apply n1; eapply map_blk_inj; et.
  Qed.

  Lemma step_sub_ptr pstate f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MGE: match_ge sk tge)
    (MM: match_mem sk tge m tm)
    sz v1 v2
    tf tcode tcont ktr bflag r mn
    (NEXT: forall ofs,
          Cop._sem_ptr_sub_join_common (map_val sk tge v1) (map_val sk tge v2) tm = Some ofs ->
          (0 < sz <= Ptrofs.max_signed)%Z ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true bflag
              (ktr (pstate, Vptrofs (Ptrofs.divs ofs (Ptrofs.repr sz))))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true bflag
      (`r0: (p_state * val) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (ccallU "sub_ptr" (sz, v1, v2)))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold ccallU. sim_red. sim_tau. ss. sim_red. unfold sub_ptrF.
    sim_tau. repeat (sim_tau; sim_red).
    rewrite PSTATE. sim_red. unfold unwrapU. remove_UBcase.
    repeat (sim_tau; sim_red). rewrite Any.upcast_downcast. sim_red.
    destruct Coqlib.zlt; destruct Coqlib.zle; ss.
    eapplyf NEXT; et; try nia.
    unfold Cop._sem_ptr_sub_join_common in *.
    des_ifs; ss; clarify.
    - unfold Cop._sem_ptr_sub_join, Cop._sem_ptr_sub in *. des_ifs.
    - unfold Cop._sem_ptr_sub_join in Heq0. des_ifs.
      + unfold Cop._sem_ptr_sub in *. des_ifs.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *.
        des_ifs. move Heq6 at bottom.
        hexploit match_to_ptr; et. i.
        hexploit match_to_int; et. i.
        simpl in Heq0. simpl in Heq4. simpl map_val in H. simpl map_val in H0.
        clarify.
        unfold Cop._sem_ptr_sub_join.
        unfold Cop._sem_ptr_sub, IntPtrRel.to_int_val, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val.
        rewrite H. rewrite H0. des_ifs.
        { simpl in Heq0. clarify. }
        { simpl in Heq0. simpl in Heq2. clarify. }
        { f_equal. symmetry. simpl in Heq2. clarify. apply Ptrofs.same_if_eq. et. }
      + unfold Cop._sem_ptr_sub in Heq1. des_ifs.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        des_ifs. move Heq3 at bottom.
        hexploit match_to_ptr; et. i.
        simpl in Heq1. simpl map_val in H. clarify.
        unfold Cop._sem_ptr_sub_join.
        unfold Cop._sem_ptr_sub, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val.
        rewrite H. des_ifs.
        all: try solve [ss; clarify].
        simpl in Heq0. unfold IntPtrRel.to_int_val in Heq5. simpl in Heq5. clarify.
        clear - Heq6 H Heq4.
        unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in Heq6.
        des_ifs. unfold Mem.to_ptr, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
        des_ifs. unfold Mem.denormalize in *. apply Maps.PTree.gselectf in Heq2.
        des. unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in Heq3.
        des_ifs; bsimpl; clarify. des.
        clear - Heq4. hexploit Ptrofs.eq_spec. rewrite Heq4. i. exfalso.
        apply H. unfold Ptrofs.of_int64, Ptrofs.sub, Int64.sub.
        apply Ptrofs.eqm_samerepr. rewrite <- Ptrofs.eqm64; et.
        eapply Int64.eqm_trans. 2:{ apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_trans.
        2:{ apply Int64.eqm_sub. apply Int64.eqm_refl. apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_trans.
        { apply Int64.eqm_sub. apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr. apply Int64.eqm_refl. }
        eapply Int64.eqm_refl2. nia.
      + unfold Cop._sem_ptr_sub in Heq2. des_ifs.
        unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *.
        des_ifs. hexploit match_to_int; et. i.
        simpl in Heq3. simpl map_val in H. clarify.
        unfold Cop._sem_ptr_sub_join.
        unfold Cop._sem_ptr_sub, IntPtrRel.to_int_val, IntPtrRel.option_to_val.
        rewrite H. des_ifs.
        { ss. clarify. f_equal. apply Ptrofs.same_if_eq. et. }
        unfold IntPtrRel.to_ptr_val in Heq7. simpl in Heq7, Heq3. clarify.
        clear - Heq6 H Heq5.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in Heq6.
        des_ifs. unfold Mem.to_ptr, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
        des_ifs. unfold Mem.denormalize in *. apply Maps.PTree.gselectf in Heq2.
        des. unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in Heq4.
        des_ifs; bsimpl; clarify. des.
        clear - Heq5. hexploit Ptrofs.eq_spec. rewrite Heq5. i. exfalso.
        apply H. unfold Ptrofs.of_int64, Ptrofs.sub, Int64.sub.
        apply Ptrofs.eqm_samerepr. rewrite <- Ptrofs.eqm64; et.
        eapply Int64.eqm_trans. 2:{ apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_trans.
        2:{ apply Int64.eqm_sub. apply Int64.eqm_refl. apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_trans.
        { apply Int64.eqm_sub. apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr. apply Int64.eqm_refl. }
        eapply Int64.eqm_refl2. nia.
    - unfold Cop._sem_ptr_sub_join, Cop._sem_ptr_sub in *. des_ifs.
    - unfold Cop._sem_ptr_sub_join in Heq0. des_ifs.
      + unfold Cop._sem_ptr_sub in *. des_ifs.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *.
        des_ifs. hexploit match_to_ptr; et. i.
        move Heq4 at bottom.
        hexploit match_to_int; et. i.
        simpl in Heq6. simpl in Heq1. simpl map_val in H. simpl map_val in H0.
        clarify.
        unfold Cop._sem_ptr_sub_join.
        unfold Cop._sem_ptr_sub, IntPtrRel.to_int_val, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val.
        rewrite H. rewrite H0. des_ifs.
        { simpl in Heq1. clarify. }
        { simpl in Heq1. simpl in Heq2. clarify. }
        { f_equal. symmetry. simpl in Heq2. clarify. apply Ptrofs.same_if_eq. et. }
      + unfold Cop._sem_ptr_sub in Heq1. des_ifs.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in *.
        des_ifs.
        hexploit match_to_ptr; et. i.
        simpl in Heq3. simpl map_val in H. clarify.
        unfold Cop._sem_ptr_sub_join.
        unfold Cop._sem_ptr_sub, IntPtrRel.to_ptr_val, IntPtrRel.option_to_val.
        rewrite H. des_ifs.
        all: try solve [ss; clarify].
        simpl in Heq0. unfold IntPtrRel.to_int_val in Heq6. simpl in Heq6. clarify.
        clear - Heq5 H Heq4.
        unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in Heq5.
        des_ifs. unfold Mem.to_ptr, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
        des_ifs. unfold Mem.denormalize in *. apply Maps.PTree.gselectf in Heq2.
        des. unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in Heq3.
        des_ifs; bsimpl; clarify. des.
        clear - Heq4. hexploit Ptrofs.eq_spec. rewrite Heq4. i. exfalso.
        apply H. unfold Ptrofs.of_int64, Ptrofs.sub, Int64.sub.
        apply Ptrofs.eqm_samerepr. rewrite <- Ptrofs.eqm64; et.
        eapply Int64.eqm_trans. 2:{ apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_trans.
        2:{ apply Int64.eqm_sub. apply Int64.eqm_unsigned_repr. apply Int64.eqm_refl. }
        eapply Int64.eqm_trans.
        { apply Int64.eqm_sub. apply Int64.eqm_refl. apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_refl2. nia.
      + unfold Cop._sem_ptr_sub in Heq2. des_ifs.
        unfold IntPtrRel.to_int_val, IntPtrRel.option_to_val in *.
        des_ifs. move Heq3 at bottom.
        hexploit match_to_int; et. i.
        simpl in Heq2. simpl map_val in H. clarify.
        unfold Cop._sem_ptr_sub_join.
        unfold Cop._sem_ptr_sub, IntPtrRel.to_int_val, IntPtrRel.option_to_val.
        rewrite H. des_ifs.
        { ss. clarify. f_equal. apply Ptrofs.same_if_eq. et. }
        unfold IntPtrRel.to_ptr_val in Heq6. simpl in Heq6, Heq2. clarify.
        clear - Heq7 H Heq5.
        unfold IntPtrRel.to_ptr_val, IntPtrRel.option_to_val in Heq7.
        des_ifs. unfold Mem.to_ptr, Mem.to_int, Mem.ptr2int_v, Mem.ptr2int in *.
        des_ifs. unfold Mem.denormalize in *. apply Maps.PTree.gselectf in Heq2.
        des. unfold Mem.denormalize_aux, Mem.is_valid, Mem.addr_is_in_block in Heq4.
        des_ifs; bsimpl; clarify. des.
        clear - Heq5. hexploit Ptrofs.eq_spec. rewrite Heq5. i. exfalso.
        apply H. unfold Ptrofs.of_int64, Ptrofs.sub, Int64.sub.
        apply Ptrofs.eqm_samerepr. rewrite <- Ptrofs.eqm64; et.
        eapply Int64.eqm_trans. 2:{ apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_trans.
        2:{ apply Int64.eqm_sub. apply Int64.eqm_unsigned_repr. apply Int64.eqm_refl. }
        eapply Int64.eqm_trans.
        { apply Int64.eqm_sub. apply Int64.eqm_refl. apply Int64.eqm_sym. apply Int64.eqm_unsigned_repr. }
        eapply Int64.eqm_refl2. nia.
    - destruct eq_block eqn:? in Heq0; clarify.
      subst. destruct eq_block; clarify.
  Qed.

  Lemma match_to_ptr_val m tm sk tge v b ofs
    (MM: match_mem sk tge m tm)
    (MGE: match_ge sk tge)
    (SVAL: IntPtrRel.to_ptr_val m v = Vptr b ofs)
  :
    IntPtrRel.to_ptr_val tm (map_val sk tge v) = Vptr (map_blk sk tge b) ofs.
  Proof.
    unfold IntPtrRel.to_ptr_val in *. destruct (Mem.to_ptr _ tm) eqn:?; destruct (Mem.to_ptr _ m) eqn:?; ss; clarify.
    - hexploit match_to_ptr; et. i. clarify.
    - hexploit match_to_ptr; et. i. clarify.
  Qed.

  Lemma match_to_int_val m tm sk tge v i
    (MM: match_mem sk tge m tm)
    (MGE: match_ge sk tge)
    (SVAL: IntPtrRel.to_int_val m v = Vlong i)
  :
    IntPtrRel.to_int_val tm (map_val sk tge v) = Vlong i.
  Proof.
    unfold IntPtrRel.to_int_val in *. destruct (Mem.to_int _ tm) eqn:?; destruct (Mem.to_int _ m) eqn:?; ss; clarify.
    - hexploit match_to_int; et. i. rewrite H in Heqo. clarify.
    - hexploit match_to_int; et. i. rewrite H in Heqo. clarify.
  Qed.

  Lemma match_cmplu_join : 
    forall (m tm : mem) (sk : Sk.t) (tge : Genv.t fundef type) (c: comparison) (v1 v2 : val) (b : bool),
      match_mem sk tge m tm ->
      match_ge sk tge ->
      IntPtrRel.cmplu_join m c v1 v2 = Some b ->
      IntPtrRel.cmplu_join tm c (map_val sk tge v1) (map_val sk tge v2) = Some b.
  Proof.
    i. unfold IntPtrRel.cmplu_join in *. unfold IntPtrRel.bool_optjoin, IntPtrRel.opt_join in H1.
    des_ifs.
    - clear Heq0.
      assert ((Val.cmplu_bool (Mem.valid_pointer tm) c (IntPtrRel.to_ptr_val tm (map_val sk tge v1)) (IntPtrRel.to_ptr_val tm (map_val sk tge v2))) = Some b0); cycle 1.
      { unfold IntPtrRel.bool_optjoin, IntPtrRel.opt_join. unfold IntPtrRel.bool_join in *.
        des_ifs. hexploit IntPtrRel.cmplu_no_angelic; et. i. red in H1. clarify.
        rewrite eqb_reflx in Heq2. clarify. }
      clear H1. unfold Val.cmplu_bool in Heq. des_ifs.
      + unfold IntPtrRel.to_ptr_val, Mem.to_ptr in Heq0, Heq1. des_ifs. ss.
        unfold Vnullptr in *. des_ifs. apply Int64.same_if_eq in Heq3, Heq2. clarify.
      + unfold IntPtrRel.to_ptr_val, Mem.to_ptr in Heq0. des_ifs. ss.
        unfold Vnullptr in *. des_ifs. apply Int64.same_if_eq in Heq5. clarify.
        eapply match_to_ptr_val in Heq1; et. rewrite Heq1.
        unfold Val.cmplu_bool. des_ifs.
        erewrite !match_valid_pointer in Heq6; et.
        unfold IntPtrRel.to_ptr_val, Mem.to_ptr in Heq0. des_ifs. ss.
        unfold Vnullptr in *. des_ifs.
      + unfold IntPtrRel.to_ptr_val, Mem.to_ptr in Heq1. des_ifs. ss.
        unfold Vnullptr in *. des_ifs. apply Int64.same_if_eq in Heq5. clarify.
        eapply match_to_ptr_val in Heq0; et. rewrite Heq0.
        unfold Val.cmplu_bool. des_ifs.
        erewrite !match_valid_pointer in Heq6; et.
        unfold IntPtrRel.to_ptr_val, Mem.to_ptr in Heq1. des_ifs. ss.
        unfold Vnullptr in *. des_ifs.
      + eapply match_to_ptr_val in Heq0; et. rewrite Heq0.
        eapply match_to_ptr_val in Heq1; et. rewrite Heq1.
        unfold Val.cmplu_bool. des_ifs.
        erewrite !match_valid_pointer in Heq; et. clarify.
      + eapply match_to_ptr_val in Heq0; et. rewrite Heq0.
        eapply match_to_ptr_val in Heq1; et. rewrite Heq1.
        unfold Val.cmplu_bool. des_ifs;
        try solve [apply map_blk_inj in e; et; clarify].
        erewrite !match_valid_pointer in Heq4; et. clarify.
    - clear Heq0.
      assert ((Val.cmplu_bool (Mem.valid_pointer tm) c (IntPtrRel.to_ptr_val tm (map_val sk tge v1)) (IntPtrRel.to_ptr_val tm (map_val sk tge v2))) = Some b); cycle 1.
      { unfold IntPtrRel.bool_optjoin, IntPtrRel.opt_join. unfold IntPtrRel.bool_join in *.
        des_ifs. hexploit IntPtrRel.cmplu_no_angelic; et. i. red in H1. clarify.
        rewrite eqb_reflx in Heq2. clarify. }
      unfold Val.cmplu_bool in Heq. des_ifs.
      + unfold IntPtrRel.to_ptr_val, Mem.to_ptr in Heq0, Heq1. des_ifs. ss.
        unfold Vnullptr in *. des_ifs. apply Int64.same_if_eq in Heq3, Heq2. clarify.
      + unfold IntPtrRel.to_ptr_val, Mem.to_ptr in Heq0. des_ifs. ss.
        unfold Vnullptr in *. des_ifs. apply Int64.same_if_eq in Heq5. clarify.
        eapply match_to_ptr_val in Heq1; et. rewrite Heq1.
        unfold Val.cmplu_bool. des_ifs.
        erewrite !match_valid_pointer in Heq6; et.
        unfold IntPtrRel.to_ptr_val, Mem.to_ptr in Heq0. des_ifs. ss.
        unfold Vnullptr in *. des_ifs.
      + unfold IntPtrRel.to_ptr_val, Mem.to_ptr in Heq1. des_ifs. ss.
        unfold Vnullptr in *. des_ifs. apply Int64.same_if_eq in Heq5. clarify.
        eapply match_to_ptr_val in Heq0; et. rewrite Heq0.
        unfold Val.cmplu_bool. des_ifs.
        erewrite !match_valid_pointer in Heq6; et.
        unfold IntPtrRel.to_ptr_val, Mem.to_ptr in Heq1. des_ifs. ss.
        unfold Vnullptr in *. des_ifs.
      + eapply match_to_ptr_val in Heq0; et. rewrite Heq0.
        eapply match_to_ptr_val in Heq1; et. rewrite Heq1.
        unfold Val.cmplu_bool. des_ifs.
        erewrite !match_valid_pointer in Heq; et. clarify.
      + eapply match_to_ptr_val in Heq0; et. rewrite Heq0.
        eapply match_to_ptr_val in Heq1; et. rewrite Heq1.
        unfold Val.cmplu_bool. des_ifs;
        try solve [apply map_blk_inj in e; et; clarify].
        erewrite !match_valid_pointer in Heq4; et. clarify.
    - clear Heq.
      assert ((Val.cmplu_bool (Mem.valid_pointer tm) c (IntPtrRel.to_int_val tm (map_val sk tge v1)) (IntPtrRel.to_int_val tm (map_val sk tge v2))) = Some b); cycle 1.
      { unfold IntPtrRel.bool_optjoin, IntPtrRel.opt_join. unfold IntPtrRel.bool_join in *.
        des_ifs. { apply eqb_prop in Heq2. clarify. }
        hexploit IntPtrRel.cmplu_no_angelic; et. i. red in H1. clarify.
        rewrite eqb_reflx in Heq2. clarify. }
      unfold Val.cmplu_bool in Heq0. des_ifs.
      + eapply match_to_int_val in Heq; et. rewrite Heq.
        eapply match_to_int_val in Heq1; et. rewrite Heq1.
        unfold Val.cmplu_bool. des_ifs.
      + unfold IntPtrRel.to_int_val, Mem.to_int in Heq1. ss. des_ifs.
      + unfold IntPtrRel.to_int_val, Mem.to_int in Heq. ss. des_ifs.
      + unfold IntPtrRel.to_int_val, Mem.to_int in Heq. ss. des_ifs.
      + unfold IntPtrRel.to_int_val, Mem.to_int in Heq. ss. des_ifs.
  Qed.

  Lemma step_cmp_ptr pstate f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MGE: match_ge sk tge)
    (MM: match_mem sk tge m tm)
    c v1 v2
    tf tcode tcont ktr bflag r mn
    (NEXT: forall b,
          Cop.cmp_ptr tm c (map_val sk tge v1) (map_val sk tge v2) = Some (Val.of_bool b) ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true bflag
              (ktr (pstate, b))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true bflag
      (`r0: (p_state * bool) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (ccallU "cmp_ptr" (c, v1, v2)))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold ccallU. step. ss. unfold cmp_ptrF. step. rewrite PSTATE. rewrite Any.upcast_downcast.
    step. unfold unwrapU. remove_UBcase. econs 3; ss. esplits. { econs. }
    step. rewrite Any.upcast_downcast. step.
    pfold_reverse. apply NEXT. unfold Cop.cmp_ptr. des_ifs.
    assert (IntPtrRel.cmplu_join_common tm c (map_val sk tge v1) (map_val sk tge v2) = Some b). 2:{ rewrite H. ss. }
    unfold IntPtrRel.cmplu_join_common in Heq0. des_ifs.
    - ss. rewrite Heq1. rewrite Heq1 in Heq0. erewrite !match_valid_pointer; et. 
    - ss. rewrite Heq1. eapply match_cmplu_join in Heq0; et.
    - ss. rewrite Heq1 in *. erewrite ! match_valid_pointer; et.
    - ss. rewrite Heq1 in *. eapply match_cmplu_join in Heq0; et.
    - ss. erewrite ! match_valid_pointer; et. destruct eq_block in Heq0.
      + clarify. destruct eq_block; clarify.
      + destruct eq_block; clarify. apply map_blk_inj in e0; et. clarify.
  Qed.


  Lemma step_non_null_ptr pstate f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    blk ofs
    tf tcode tcont ktr bflag r mn
    (NEXT: Mem.weak_valid_pointer tm (map_blk sk tge blk) (Ptrofs.unsigned ofs) = true ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true bflag
              (ktr (pstate, true))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true bflag
      (`r0: (p_state * bool) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (ccallU "non_null?" (Vptr blk ofs)))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold ccallU. sim_red. sim_tau. ss. sim_red. unfold non_nullF. sim_red. repeat (sim_tau; sim_red).
    rewrite PSTATE. sim_red. remove_UBcase. repeat (sim_tau; sim_red).
    eapplyf NEXT; et.
    unfold Mem.weak_valid_pointer, Mem.valid_pointer. inv MM.
    repeat (match goal with | |- context ctx [ Mem.perm_dec ?x ] => destruct (Mem.perm_dec x) end)
    ; et; ss; unfold Mem.perm in *; rewrite <- MEM_PERM in *.
    unfold Mem.weak_valid_pointer, Mem.valid_pointer in Heq.
    destruct Mem.perm_dec in Heq; clarify.
    destruct Mem.perm_dec in Heq; clarify.
  Qed.

  Lemma step_bool_val pstate f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ3: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    v ty
 r bflag tcode tf tcont mn ktr
    (NEXT: forall b,
            Cop.bool_val (map_val sk tge v) ty tm = Some b ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true bflag
              (ktr (pstate, b))
              (State tf tcode tcont te tle tm))
  :
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true bflag
      (`r0: (p_state * bool) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (bool_val_c v ty))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold bool_val_c.
    remove_UBcase; try solve [eapply NEXT; unfold Cop.bool_val; rewrite Heq; et].
    eapply step_non_null_ptr; et. i.
    eapply NEXT; unfold Cop.bool_val; rewrite Heq; ss; des_ifs.
  Qed.

  Lemma step_sem_cast pstate f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    v ty1 ty2
    tf tcode tcont ktr b r mn
    (NEXT: forall v',
            Cop.sem_cast (map_val sk tge v) ty1 ty2 tm = Some (map_val sk tge v') ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              (ktr (pstate, v'))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * val) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (sem_cast_c v ty1 ty2))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold sem_cast_c. des_ifs_safe. unfold cast_to_ptr. remove_UBcase.
    all: try solve [eapplyf NEXT; unfold Cop.sem_cast; des_ifs].
    all: try solve [unfold unwrapU; remove_UBcase; eapplyf NEXT; unfold Cop.sem_cast; des_ifs; ss; clarify].
    eapply step_non_null_ptr; et. i. sim_red. eapplyf NEXT; et.
    unfold Cop.sem_cast. rewrite Heq1; des_ifs_safe.
    ss. clarify.
  Qed.

  Lemma step_assign_loc pstate f_table modl cprog sk_mem sk tge le tle e te m tm ce tce
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MCE: match_ce ce tce)
    (MM: match_mem sk tge m tm)
    ty vp v
    tf tcode tcont ktr b r mn
    (NEXT: forall tm' m',
            match_mem sk tge m' tm' ->
            assign_loc tce ty tm (map_val sk tge vp) (map_val sk tge v) tm' ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, ()))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * ())<-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (assign_loc_c ce ty vp v))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold assign_loc_c. des_ifs; try sim_red; try sim_triggerUB.
    - eapply step_store; et. i. eapply NEXT; et. econs; et.
    - eapply step_memcpy; et. i. sim_red. eapply NEXT; et.
      inv H. 2:{ econs 3; et. erewrite match_sizeof; et. }
      erewrite <- !match_sizeof in *; et.
      erewrite <- !match_alignof_blockcopy in *; et.
      econs 2; et.
  Qed.

  Lemma step_deref_loc pstate f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    ty vp
    tf tcode tcont ktr b r mn
    (NEXT: forall v,
            deref_loc ty tm (map_val sk tge vp) (map_val sk tge v) ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              (ktr (pstate, v))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * val) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (deref_loc_c ty vp))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold deref_loc_c. remove_UBcase.
    - eapply step_load; et. i. eapplyf NEXT; ss; econs; et.
    - eapplyf NEXT; ss; econs 2; et.
    - eapplyf NEXT; ss; econs 3; et.
  Qed.

  Lemma step_unary_op pstate f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    uop v ty
    tf tcode tcont ktr b r mn
    (NEXT: forall v',
            Cop.sem_unary_operation uop (map_val sk tge v) ty tm = Some (map_val sk tge v') ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              (ktr (pstate, v'))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * val) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (unary_op_c uop v ty))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold unary_op_c. des_ifs; sim_red.
    - unfold bool_val_c. remove_UBcase.
      + apply NEXT. unfold Cop.sem_unary_operation. unfold Cop.sem_notbool. ss. unfold Cop.bool_val. rewrite Heq. ss. unfold Val.of_bool. des_ifs.
      + apply NEXT. unfold Cop.sem_unary_operation. unfold Cop.sem_notbool. ss. unfold Cop.bool_val. rewrite Heq. ss. unfold Val.of_bool. des_ifs.
      + eapply step_non_null_ptr; et. i. sim_red. apply NEXT. unfold Cop.sem_unary_operation, Cop.sem_notbool, Cop.bool_val. rewrite Heq. ss. rewrite H. des_ifs.
      + apply NEXT. unfold Cop.sem_unary_operation. unfold Cop.sem_notbool. ss. unfold Cop.bool_val. rewrite Heq. ss. unfold Val.of_bool. des_ifs.
      + apply NEXT. unfold Cop.sem_unary_operation. unfold Cop.sem_notbool. ss. unfold Cop.bool_val. rewrite Heq. ss. unfold Val.of_bool. des_ifs.
    - unfold unwrapU. remove_UBcase. apply NEXT.
      unfold Cop.sem_unary_operation, Cop.sem_notint in *.
      des_ifs; ss; clarify.
    - unfold unwrapU. remove_UBcase. apply NEXT.
      unfold Cop.sem_unary_operation, Cop.sem_neg in *.
      des_ifs; ss; clarify.
    - unfold unwrapU. remove_UBcase. apply NEXT.
      unfold Cop.sem_unary_operation, Cop.sem_absfloat in *.
      des_ifs; ss; clarify.
  Qed.

  Lemma step_binary_op pstate f_table modl cprog sk_mem sk tge ce tce le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MCE: match_ce ce tce)
    (MM: match_mem sk tge m tm)
    biop v1 ty1 v2 ty2
    tf tcode tcont ktr b r mn
    (NEXT: forall v',
            Cop.sem_binary_operation tce biop (map_val sk tge v1) ty1 (map_val sk tge v2) ty2 tm = Some (map_val sk tge v') ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              (ktr (pstate, v'))
              (State tf tcode tcont te tle tm))
:
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * val) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (binary_op_c ce biop v1 ty1 v2 ty2))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    unfold binary_op_c. des_ifs; unfold sem_add_c, sem_sub_c, sem_mul_c, sem_div_c, sem_mod_c, sem_and_c, sem_or_c, sem_xor_c, Cop.sem_shl, Cop.sem_shr, sem_cmp_c.
    - des_ifs.
      + unfold sem_add_ptr_int_c. remove_UBcase.
        all: apply NEXT; erewrite <- match_sizeof; et; unfold Cop.sem_binary_operation, Cop.sem_add, Cop.sem_add_ptr_int; ss; des_ifs.
      + unfold sem_add_ptr_long_c. remove_UBcase.
        all: apply NEXT; erewrite <- match_sizeof; et; unfold Cop.sem_binary_operation, Cop.sem_add, Cop.sem_add_ptr_long; ss; des_ifs.
      + unfold sem_add_ptr_int_c. remove_UBcase.
        all: apply NEXT; erewrite <- match_sizeof; et; unfold Cop.sem_binary_operation, Cop.sem_add, Cop.sem_add_ptr_int; ss; des_ifs.
      + unfold sem_add_ptr_long_c. remove_UBcase.
        all: apply NEXT; erewrite <- match_sizeof; et; unfold Cop.sem_binary_operation, Cop.sem_add, Cop.sem_add_ptr_long; ss; des_ifs.
      + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
        eapply step_sem_cast; et. i. remove_UBcase.
        all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_add, Cop.sem_binarith; rewrite Heq; rewrite Heq0; des_ifs.
    - remove_UBcase.
      + apply NEXT. erewrite <- match_sizeof; et. unfold Cop.sem_binary_operation, Cop.sem_sub. ss; des_ifs.
      + apply NEXT. erewrite <- match_sizeof; et. unfold Cop.sem_binary_operation, Cop.sem_sub. ss; des_ifs.
      + eapply step_sub_ptr; et. i. apply NEXT.
        erewrite <- match_sizeof in *; et. unfold Cop.sem_binary_operation, Cop.sem_sub. ss; des_ifs.
        destruct Coqlib.zle; destruct Coqlib.zlt; ss; try nia.
      + apply NEXT. erewrite <- match_sizeof; et. unfold Cop.sem_binary_operation, Cop.sem_sub. ss; des_ifs.
      + apply NEXT. erewrite <- match_sizeof; et. unfold Cop.sem_binary_operation, Cop.sem_sub. ss; des_ifs.
      + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
        eapply step_sem_cast; et. i. remove_UBcase.
        all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_sub, Cop.sem_binarith; rewrite Heq; rewrite Heq0; des_ifs.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_mul, Cop.sem_binarith; rewrite Heq; des_ifs.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_div, Cop.sem_binarith; rewrite Heq; des_ifs.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_mod, Cop.sem_binarith; rewrite Heq; des_ifs.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_and, Cop.sem_binarith; rewrite Heq; des_ifs.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_or, Cop.sem_binarith; rewrite Heq; des_ifs.
    - unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
      eapply step_sem_cast; et. i. remove_UBcase.
      all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_xor, Cop.sem_binarith; rewrite Heq; des_ifs.
    - unfold unwrapU. remove_UBcase.
       eapplyf NEXT. i; clarify; unfold Cop.sem_binary_operation, Cop.sem_shl; unfold Cop.sem_binarith;
        unfold Cop.sem_shift in *; des_ifs; ss; clarify.
    - unfold unwrapU. remove_UBcase.
      eapplyf NEXT; i; clarify; unfold Cop.sem_binary_operation, Cop.sem_shr; unfold Cop.sem_binarith;
        unfold Cop.sem_shift in *; des_ifs; ss; clarify.
    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. simpl. unfold Cop.sem_cmp. des_ifs.
        simpl map_val in H.
        rewrite H. unfold Val.of_bool. des_ifs.
      + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
        eapply step_sem_cast; et. i. remove_UBcase.
        all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
        all: unfold Val.of_bool; des_ifs; ss; clarify.
    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. simpl. unfold Cop.sem_cmp. des_ifs.
        simpl map_val in H.
        rewrite H. unfold Val.of_bool. des_ifs.
      + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
        eapply step_sem_cast; et. i. remove_UBcase.
        all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
        all: unfold Val.of_bool; des_ifs; ss; clarify.
    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. simpl. unfold Cop.sem_cmp. des_ifs.
        simpl map_val in H.
        rewrite H. unfold Val.of_bool. des_ifs.
      + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
        eapply step_sem_cast; et. i. remove_UBcase.
        all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
        all: unfold Val.of_bool; des_ifs; ss; clarify.
    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. simpl. unfold Cop.sem_cmp. des_ifs.
        simpl map_val in H.
        rewrite H. unfold Val.of_bool. des_ifs.
      + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
        eapply step_sem_cast; et. i. remove_UBcase.
        all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
        all: unfold Val.of_bool; des_ifs; ss; clarify.
    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. simpl. unfold Cop.sem_cmp. des_ifs.
        simpl map_val in H.
        rewrite H. unfold Val.of_bool. des_ifs.
      + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
        eapply step_sem_cast; et. i. remove_UBcase.
        all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
        all: unfold Val.of_bool; des_ifs; ss; clarify.
    - destruct Cop.classify_cmp eqn:?; remove_UBcase.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. ss. unfold Cop.sem_cmp. des_ifs.
        unfold Vptrofs in *. des_ifs. ss.
        rewrite H. unfold Val.of_bool. des_ifs.
      + eapply step_cmp_ptr; et. i. sim_red. eapply NEXT. simpl. unfold Cop.sem_cmp. des_ifs.
        simpl map_val in H.
        rewrite H. unfold Val.of_bool. des_ifs.
      + unfold sem_binarith_c. sim_red. eapply step_sem_cast; et. i. sim_red.
        eapply step_sem_cast; et. i. remove_UBcase.
        all: apply NEXT; unfold Cop.sem_binary_operation, Cop.sem_cmp, Cop.sem_binarith; rewrite Heq; des_ifs.
        all: unfold Val.of_bool; des_ifs; ss; clarify.
  Qed.

  Lemma _step_eval pstate ge ce tce f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: tce = ge.(genv_cenv))
    (EQ2: tge = ge.(genv_genv))
    (EQ3: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MCE: match_ce ce tce)
    (MM: match_mem sk tge m tm)
 r b tcode tf tcont mn a
 :
  (forall ktr1,
    (forall vp,
      eval_lvalue ge te tle tm a (map_val sk tge vp) ->
      paco4
        (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
        (ktr1 (pstate, vp))
        (State tf tcode tcont te tle tm))
    ->
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * val) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_lvalue_c sk ce e le a))
          pstate);; ktr1 r0)
      (State tf tcode tcont te tle tm))
  /\
  (forall ktr2,
    (forall v,
      eval_expr ge te tle tm a (map_val sk tge v) ->
      paco4
        (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
        (ktr2 (pstate, v))
        (State tf tcode tcont te tle tm))
    ->
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * Values.val) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_expr_c sk ce e le a))
          pstate);; ktr2 r0)
      (State tf tcode tcont te tle tm)).
  Proof.
    induction a.
    1,2,3,4 : split; i; remove_UBcase; eapply H; try econs.
    2,4,5,6,7 : des; split; i; remove_UBcase; ss.
    - split; i; ss.
      + remove_UBcase; eapply H; et.
        * econs. eapply env_match_some in ME; et.
        * econs 2; try solve [eapply env_match_none; et]. inv MGE. unfold valid_check in Heq.
          destruct Pos.eq_dec; ss. rewrite e0. eapply MGE0; et.
      + remove_UBcase; eapply step_deref_loc; et; i; sim_red; eapply H; et; econs; et.
        * econs. hexploit env_match_some; et.
        * econs 2; try solve [eapply env_match_none; et]. inv MGE. unfold valid_check in Heq.
          destruct Pos.eq_dec; ss. rewrite e0. eapply MGE0; et.
    - unfold unwrapU. remove_UBcase. eapply H; et. econs. inv MLE. eapply ML. et.
    - eapply IHa. i. eapply H; et. econs; et.
    - eapply IHa0. i. eapply step_unary_op; et. i. eapply H; et. econs; et.
    - eapply IHa3. i. sim_red. eapply IHa0. i. eapply step_binary_op; et.
      i. eapply H; et. econs; et.
    - eapply IHa0. i. eapply step_sem_cast; et. i. eapply H; et. econs; et.
    - des; split; i; ss; remove_UBcase; eapply IHa0; i; remove_UBcase.
      + eapply H. econs; et. destruct v; ss.
      + eapply step_deref_loc; et. i. sim_red. eapply H. econs; et. econs;et. destruct v; ss.
    - des. split; i; ss; sim_red; eapply IHa0; i; subst.
      + remove_UBcase; unfold unwrapU; remove_UBcase; remove_UBcase; eapply H; et.
        * econs; et. { destruct v; ss. }
          { inv MCE. rewrite <- MCE0 in Heq2. apply Maps.PTree.elements_complete. et. }
          2:{ des_ifs. destruct v; ss. }
          { unfold ClightPlusExprgen.field_offset in Heq3.
            clear - Heq3 MCE. unfold field_offset. set 0%Z as d in *.
            clearbody d. destruct c. ss. revert i d Heq3.
            induction co_members; ss. i. des_ifs.
            { erewrite match_alignof; et. } apply IHco_members.
            erewrite match_alignof; et. erewrite match_sizeof; et. }
        * econs 5; et. { destruct v; ss. }
          inv MCE. rewrite <- MCE0 in Heq1. apply Maps.PTree.elements_complete. et.
      + remove_UBcase; unfold unwrapU; remove_UBcase; remove_UBcase;
        eapply step_deref_loc; et; i; sim_red; eapply H; et; econs; et.
        * econs; et. { destruct v; ss. }
          { inv MCE. rewrite <- MCE0 in Heq2. apply Maps.PTree.elements_complete. et. }
          2:{ des_ifs. destruct v; ss. }
          { unfold ClightPlusExprgen.field_offset in Heq3.
            clear - Heq3 MCE. unfold field_offset. set 0%Z as d in *.
            clearbody d. destruct c. ss. revert i d Heq3.
            induction co_members; ss. i. des_ifs.
            { erewrite match_alignof; et. } apply IHco_members.
            erewrite match_alignof; et. erewrite match_sizeof; et. }
        * econs 5; et. { destruct v; ss. }
          inv MCE. rewrite <- MCE0 in Heq1. apply Maps.PTree.elements_complete. et.
    - split; i.
      + ss. remove_UBcase.
      + ss. sim_red. apply H.
        replace (map_val sk _ _) with (Vptrofs (Ptrofs.repr (ClightPlusExprgen.sizeof ce t0))).
        2:{ unfold Vptrofs. des_ifs. }
        erewrite <- match_sizeof; et.
        replace tce with (ge.(genv_cenv)). econs.
    - split; i.
      + ss. remove_UBcase.
      + ss. sim_red. apply H.
        replace (map_val sk _ _) with (Vptrofs (Ptrofs.repr (ClightPlusExprgen.alignof ce t0))).
        2:{ unfold Vptrofs. des_ifs. }
        erewrite <- match_alignof; et.
        replace tce with (ge.(genv_cenv)). econs.
  Qed.

  Lemma step_eval_lvalue pstate ge tce ce f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: tce = ge.(genv_cenv))
    (EQ2: tge = ge.(genv_genv))
    (EQ3: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MCE: match_ce ce tce)
    (MM: match_mem sk tge m tm)
 r b tcode tf tcont mn a ktr
    (NEXT: forall vp,
            eval_lvalue ge te tle tm a (map_val sk tge vp) ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              (ktr (pstate, vp))
              (State tf tcode tcont te tle tm))
  :
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * val) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_lvalue_c sk ce e le a))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof. hexploit _step_eval; et. i. des. et. Qed.

  Lemma step_eval_expr pstate ge tce ce f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: tce = ge.(genv_cenv))
    (EQ2: tge = ge.(genv_genv))
    (EQ3: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MCE: match_ce ce tce)
    (MM: match_mem sk tge m tm)
 r b tcode tf tcont mn a ktr
    (NEXT: forall v v',
            eval_expr ge te tle tm a v ->
            v = map_val sk tge v' ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              (ktr (pstate, v'))
              (State tf tcode tcont te tle tm))
  :
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * Values.val) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_expr_c sk ce e le a))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof. hexploit _step_eval; et. i. des. et. Qed.


  Lemma step_eval_exprlist pstate ge tce ce f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: tce = ge.(genv_cenv))
    (EQ2: tge = ge.(genv_genv))
    (EQ3: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MCE: match_ce ce tce)
    (MM: match_mem sk tge m tm)
    al tyl
 r b tcode tf tcont mn ktr
    (NEXT: forall vl,
            eval_exprlist ge te tle tm al tyl (List.map (map_val sk tge) vl) ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              (ktr (pstate, vl))
              (State tf tcode tcont te tle tm))
  :
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * list Values.val) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (eval_exprlist_c sk ce e le al tyl))
          pstate);; ktr r0)
      (State tf tcode tcont te tle tm).
  Proof.
    depgen tyl. revert ktr. induction al; i.
    - ss. remove_UBcase. eapplyf NEXT. econs.
    - ss. remove_UBcase. eapply step_eval_expr; et. i. clarify. sim_red. eapply IHal. i.
      sim_red. eapply step_sem_cast; et. i. sim_red. eapplyf NEXT. econs; et.
  Qed.

End PROOF.
