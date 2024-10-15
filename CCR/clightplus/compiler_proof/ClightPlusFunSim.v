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
Require Import ClightPlusgen.
Require Import STS2SmallStep.
Require Import ClightPlusMem0.

Require Import ClightPlusMatchEnv.
Require Import ClightPlusMatchStmt.
Require Import ClightPlusLenvSim.
Require Import ClightPlusMemSim.

From compcert Require Import Values Ctypes Clight Clightdefs.


Section PROOF.

  Import ModSemL.

  Let _sim_mon := Eval simpl in (fun (src: ModL.t) (tgt: Clight.program) => @sim_mon (ModL.compile src) (semantics3 tgt)).
  Hint Resolve _sim_mon: paco.

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); try pfold; econs 3; ss; clarify; eexists; exists (step_tau _).

  Let oeq [A] (a: A) b: Prop := (a = b).
  Opaque oeq.

  Ltac to_oeq :=
    match goal with
    | |- ?A = ?B => change (oeq A B)
    end.

  Ltac from_oeq :=
    match goal with
    | |- oeq ?A ?B => change (A = B)
    end.

  Ltac sim_redE :=
    to_oeq; cbn; repeat (Red.prw ltac:(_red_gen) 1 0); repeat (Red.prw ltac:(_red_gen) 2 0); from_oeq.

  Ltac solve_ub := des; irw in H; dependent destruction H; clarify.
  Ltac sim_triggerUB :=
    (try rename H into HH); ss; unfold triggerUB; try sim_red; try pfold; econs 5; i; ss; auto;
                        [solve_ub | irw in  STEP; dependent destruction STEP; clarify].

  Ltac remove_UBcase := des_ifs; try sim_red; try solve [sim_triggerUB].

  Ltac step := repeat (sim_red; try sim_tau).

  Ltac uhu :=
    match goal with
    | |- _sim _ _ _ _ _ (_ <- (unwrapU ?x);; _) _ =>
      let t := fresh in
      set (unwrapU x) as t; unfold unwrapU in t; unfold t; clear t
    end.

  Ltac eapplyf NEXT := let X := fresh "X" in hexploit NEXT;[..|intro X; punfold X; et].

  Local Opaque Pos.of_nat.

  Local Opaque Pos.of_succ_nat.

  Lemma _step_freeing_stack cprog f_table modl sk_mem sk ge tge ce tce e te pstate m
    (EQ1: tce = ge.(genv_cenv))
    (EQ2: tge = ge.(genv_genv))
    (EQ3: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MCE: match_ce ce tce)
    (ME: match_e sk tge e te)
    (PSTATE: pstate "Mem"%string = m↑)
  r b tstate mn ktr
    (NEXT: forall m',
      Mem.free_list m (List.map (map_fst (fun b => pair b 0%Z)) (ClightPlusExprgen.blocks_of_env ce e)) = Some m' ->
      paco4
        (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
        (ktr (update pstate "Mem" m'↑, ()))
        tstate)
  :
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * ()) <-
        (EventsL.interp_Es (prog f_table)
          (transl_all mn (free_list_aux (ClightPlusExprgen.blocks_of_env ce e)))
          pstate)
        ;; ktr r0)
      tstate.
  Proof.
    subst.
    set (ClightPlusExprgen.blocks_of_env ce e) as l in *. clearbody l.
    depgen m. depgen pstate. induction l; i; ss.
    - sim_red. replace pstate with (update pstate "Mem" m↑).
      2:{ rewrite <- PSTATE. unfold update. apply func_ext. i. des_ifs. }
      eapply NEXT; et.
    - des_ifs_safe. unfold ccallU. step. unfold sfreeF. step.
      rewrite PSTATE. step. uhu. remove_UBcase. sim_tau. step.
      eapplyf IHl. et. i.
      replace (update (update _ _ _) _ _) with (update pstate "Mem" m'↑); et.
      unfold update. apply func_ext. i. des_ifs.
  Qed.

  Lemma step_freeing_stack cprog f_table modl ge sk_mem sk tge tce ce e te pstate m tm
    (EQ1: tce = ge.(genv_cenv))
    (EQ2: tge = ge.(genv_genv))
    (EQ3: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (PSTATE: pstate "Mem"%string = m↑)
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MCE: match_ce ce tce)
    (MM: match_mem sk tge m tm)
  r b tstate mn ktr
    (NEXT: forall m' tm',
      Mem.free_list tm (Clight.blocks_of_env ge te) = Some tm' ->
      match_mem sk tge m' tm' ->
      paco4
        (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
        (ktr (update pstate "Mem" m'↑, ()))
        tstate)
  :
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * ()) <-
        (EventsL.interp_Es (prog f_table)
          (transl_all mn (free_list_aux (ClightPlusExprgen.blocks_of_env ce e)))
          pstate)
        ;; ktr r0)
      tstate.
  Proof.
    eapply _step_freeing_stack; et. i. eapply match_mem_free_list in H; et.
    des. eapplyf NEXT; et.
  Qed.

  Lemma update_shadow V pstate (x: string) (v v': V) : update (update pstate x v) x v' = update pstate x v'.
  Proof. unfold update. apply func_ext. i. des_ifs. Qed.

  Lemma step_alloc pstate f_table modl cprog sk_mem sk tge m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (MM: match_mem sk tge m tm)
    sz
    tstate ktr b r mn
    (NEXT: forall tm' m' blk,
            Mem.alloc tm 0 sz = (tm', map_blk sk tge blk) ->
            match_mem sk tge m' tm' ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, blk))
              tstate)
:
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: p_state * block <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (ccallU "salloc" sz))
          pstate);; ktr r0)
      tstate.
  Proof.
    unfold ccallU. step. ss. step. unfold sallocF. step.
    rewrite PSTATE. step. remove_UBcase. sim_tau. step.
    hexploit match_mem_alloc; et. i. des. eapplyf NEXT; et.
  Qed.

  Lemma step_alloc_variables pstate ge tce ce f_table modl cprog sk_mem sk tge e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: tce = ge.(genv_cenv))
    (EQ2: tge = ge.(genv_genv))
    (EQ3: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MCE: match_ce ce tce)
    (MM: match_mem sk tge m tm)
    l
 r b tstate mn ktr
    (NEXT: forall e' te' m' tm',
            alloc_variables ge te tm l te' tm' ->
            match_mem sk tge m' tm' ->
            match_e sk tge e' te' ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, e'))
              tstate)
  :
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * ClightPlusExprgen.env) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (alloc_variables_c ce e l))
          pstate);; ktr r0)
      tstate.
  Proof.
    depgen e. depgen te. depgen pstate. depgen m. revert tm. depgen l. induction l; i.
    - ss. sim_red.
      replace pstate with (update pstate "Mem" m↑)
        by now unfold update; apply func_ext; i; des_ifs.
      eapply NEXT; et. econs; et.
    - ss. remove_UBcase. eapply step_alloc with (modl:=modl) (sk_mem:=sk_mem); et. i. eapply IHl; et.
      2:{ eapply match_update_e; et. }
      i. rewrite update_shadow. eapply NEXT; et. econs; et.
      erewrite match_sizeof; et.
  Qed.

  Lemma norepet l : id_list_norepet_c l = true -> Coqlib.list_norepet l.
  Proof. induction l; i; econs; try eapply IHl; unfold id_list_norepet_c in *; des_ifs; inv l0; et. Qed.

  Lemma disjoint l l' : id_list_disjoint_c l l' = true -> Coqlib.list_disjoint l l'.
  Proof.
    revert l'. induction l; i; ss.
    unfold Coqlib.list_disjoint. i. unfold id_list_disjoint_c in *. des_ifs.
    unfold Coqlib.list_disjoint in *. eapply l0; et.
  Qed.

  Lemma step_function_entry pstate ge tce ce f_table modl cprog sk_mem sk tge m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ1: tce = ge.(genv_cenv))
    (EQ2: tge = ge.(genv_genv))
    (EQ3: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (MCE: match_ce ce tce)
    (MM: match_mem sk tge m tm)
    f vl
 r b tstate mn ktr
    (NEXT: forall e' le' te' tle' m' tm',
            function_entry2 ge f (List.map (map_val sk tge) vl) tm te' tle' tm' ->
            match_mem sk tge m' tm' ->
            match_e sk tge e' te' ->
            match_le sk tge le' tle' ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              (ktr (update pstate "Mem" m'↑, (e', le')))
              tstate)
  :
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * (ClightPlusExprgen.env * ClightPlusExprgen.temp_env)) <-
        (EventsL.interp_Es
          (prog f_table)
          (transl_all mn (function_entry_c ce f vl))
          pstate);; ktr r0)
      tstate.
  Proof.
    unfold function_entry_c. remove_UBcase.
    eapply step_alloc_variables with (te := empty_env) (modl:=modl) (sk_mem := sk_mem); et.
    { econs; ss. econs. }
    i. sim_red. unfold unwrapU. remove_UBcase.
    hexploit (@match_bind_parameter_temps sk ge); et.
    - instantiate (1:=create_undef_temps (fn_temps f)). econs. i. clear -H2. set (fn_temps f) as l in *. clearbody l.
      induction l; ss. destruct a. destruct (Pos.eq_dec id i).
      { subst. rewrite Maps.PTree.gss. ss. rewrite eq_rel_dec_correct in H2. des_ifs. }
      rewrite Maps.PTree.gso; et. ss. rewrite eq_rel_dec_correct in H2. des_ifs.
      apply IHl; et.
    - i. des. eapply NEXT; et. bsimpl. des.
      econs; et. { apply norepet; et. } { apply norepet; et. }
      apply disjoint; et.
  Qed.

  Lemma return_cont pstate f_table modl cprog sk_mem sk tge le tle e te m tm
    (PSTATE: pstate "Mem"%string = m↑)
    (EQ3: f_table = (ModL.add (Mem sk_mem) modl).(ModL.enclose))
    (MGE: match_ge sk tge)
    (ME: match_e sk tge e te)
    (MLE: match_le sk tge le tle)
    (MM: match_mem sk tge m tm)
    itr_cont v
    r b tstate tcont ty mn ms ce
    (MCONT: match_cont sk tge ce ms ty mn itr_cont tcont)
    (NEXT: forall itr_cont'' itr_cont',
            match_cont sk tge ce ms ty mn itr_cont' (call_cont tcont) ->
            itr_cont'' =
              (`r0: (p_state * val) <- itr_cont' (pstate, (e, le, None, Some v));;
                let (_, retv) := r0 in Ret retv↑) ->
            paco4
              (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
              itr_cont''
              tstate)
  :
    paco4
      (_sim (ModL.compile (ModL.add (Mem sk_mem) modl)) (semantics3 cprog)) r true b
      (`r0: (p_state * val) <- itr_cont (pstate, (e, le, None, Some v));;
        let (_, retv) := r0 in Ret retv↑)
      tstate.
  Proof.
    depgen v. induction MCONT; i.
    - rewrite ITR. ss. unfold Es_to_eventE. sim_red. eapply IHMCONT; et.
    - rewrite ITR. ss. unfold Es_to_eventE. sim_red. eapply IHMCONT; et.
    - rewrite ITR. ss. unfold Es_to_eventE. sim_red. eapply IHMCONT; et.
    - ss. eapply NEXT; et. econs; et.
    - rewrite ITR. ss. unfold Es_to_eventE.
      sim_red. eapply NEXT. { econs; et. }
      rewrite ITR. unfold ktree_of_cont_itree, Es_to_eventE.
      sim_redE. et.
  Qed.

End PROOF.

