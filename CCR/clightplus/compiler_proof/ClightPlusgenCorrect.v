From compcert Require Import Coqlib Behaviors Integers Floats AST Globalenvs Linking Ctypes Cop Clight Clightdefs.

Require Import CoqlibCCR.
Require Import ITreelib.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import IRed.

Require Import ClightPlusMem0.
Require Import ClightPlusExprgen ClightPlusgen ClightPlusSkel.

Require Import ClightPlusMatchEnv.
Require Import ClightPlusLenvSim.
Require Import ClightPlusMemSim.
Require Import ClightPlusMatchStmt.

Require Import STS2SmallStep.
Require Import ClightPlusExprSim.
Require Import ClightPlusFunSim.
Require Import ClightPlusSimAll.

Require Import ClightPlusInitProof.

Definition compile_val mdl := @ModL.compile _ EMSConfigC mdl.

Definition clightp_sem sk_mem mdl := compile_val (ModL.add (Mod.lift (Mem sk_mem)) mdl).

Definition clightp_initial_state sk_mem mdl := (clightp_sem sk_mem mdl).(STS.initial_state).

Section PROOFSINGLE.

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0. (* these are itree normalization tactic *)
  Ltac sim_tau := (try sim_red); try pfold; econs 3; ss; clarify; eexists; exists (ModSemL.step_tau _).

  Ltac solve_ub := des; irw in H; dependent destruction H; clarify.
  Ltac sim_triggerUB :=
    (try rename H into HH); ss; unfold triggerUB; try sim_red; try pfold; econs 5; i; ss; auto;
                        [solve_ub | irw in  STEP; dependent destruction STEP; clarify].

  Let arrow (A B: Prop): Prop := A -> B.
  Opaque arrow.

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

  Ltac tgt_step := try pfold; econs 4; eexists; eexists.

  Ltac wrap_up := try pfold; econs 7; et; right.

  Local Opaque ident_of_string.
  Arguments Es_to_eventE /.
  Arguments itree_of_stmt /.
  Arguments sloop_iter_body_two /.
  Arguments ktree_of_cont_itree /.

  (* The thm is targeting closed program *)
  Theorem single_compile_behavior_improves
          gvmap clight_prog md sk_mem mn left_st right_st
          (COMP: compile clight_prog mn = Errors.OK md)
          (MEMSKEL: mem_skel clight_prog = Errors.OK sk_mem)
          (SINIT: left_st = clightp_initial_state sk_mem md)
          (TINIT: Clight.initial_state clight_prog right_st)
        :
          <<IMPROVES: @improves2 _ (semantics3 clight_prog) gvmap left_st right_st>>.
  Proof.
    eapply adequacy; eauto.
    { apply Clight_wf_semantics. }
    red. ss; clarify. unfold clightp_initial_state. ss; clarify. inv TINIT.
    unfold ModSemL.initial_itr. unfold ge in *. clear ge.
    rename H into INIT_TMEM, H0 into TMAINN_TBLOCK, H1 into TBLOCK_TMAINF, H2 into TMAIN_TYPE, f into tmainf.

    (* remove not-wf-(mem+md) case *)
    unfold ModL.wf_bool. destruct ModL.wf_dec; ss; [|sim_triggerUB].
    grind. unfold ITree.map. sim_red.

    (* if we find "main" in md, prog_main clight_prog in clight_prog, two functions should have same compilation relation *)
    destruct (alist_find "main" _) eqn:SMAINN_MAINF;[|sim_triggerUB].
    rewrite alist_find_map_snd in SMAINN_MAINF. uo; des_ifs; ss.
    hexploit in_tgt_prog_defs_decomp; et. i. des. clarify.
    hexploit in_tgt_prog_main; et. i. rewrite H in *.
    hexploit tgt_genv_match_symb_def; et. { unfold Genv.find_funct_ptr in TBLOCK_TMAINF. des_ifs. }
    i. clarify. rename f into tmainf.

    unfold cfunU. sim_red. unfold decomp_func. sim_red.
    change (paco4 (_sim _ _) bot4) with (sim (clightp_sem sk_mem md) (semantics3 clight_prog)).
    eapply sim_bot_flag_up with (b0 := true) (b1 := false).

    set (sort _) as sk_init in *.
    hexploit compile_match_genv; et. i.
    hexploit compile_init_mem_success; et. i. des. rewrite H3 in INIT_TMEM. clarify.
    eapply step_function_entry with (modl:=md) (ge:=globalenv clight_prog) (sk:=sk_init); et.
    { unfold get_ce. ss. econs. split; i.
      - apply alist_find_some_iff; et. rewrite CoqlibC.NoDup_norepet. apply Maps.PTree.elements_keys_norepet.
      - eapply alist_find_some; et. }
    { unfold sk_init. ss. rewrite H2. et. }
    i. pfold. econs 4. { i. inv H9. et. } { eexists. econs. et. }
    i. inv STEP. ss. unfold hide in H5. inv H5. inv H14.
    rewrite H13 in *. clarify. hexploit alloc_variables_determ;[apply H12|apply H17|].
    i. des. clarify. econs 8; et. left.

    eapply match_states_sim; et.
    { i. ss. clear - COMP H14. unfold compile, get_sk in COMP. des_ifs. ss.
      clear - H14. apply in_map_iff in H14. des. destruct x. ss. clarify.
      apply filter_In in H0. des. ss. des_ifs. et. }
    { i. clear -MEMSKEL H14. unfold mem_skel, get_sk in MEMSKEL. des_ifs.
      apply in_map_iff in H14. des. destruct x. ss. clarify. bsimpl. des.
      apply incl_filter in H0. rewrite forallb_forall in Heq3.
      hexploit Heq3; et. i. ss. destruct Pos.eq_dec; clarify. }
    { i. clear -MEMSKEL H14. unfold mem_skel, get_sk in MEMSKEL. des_ifs.
      apply in_map_iff in H14. des. destruct x. ss. clarify. bsimpl. des.
      apply incl_filter in H0. rewrite forallb_forall in Heq3.
      hexploit Heq3; et. i. ss. destruct Pos.eq_dec; clarify. }
    { i. clear -MEMSKEL H14. unfold mem_skel, get_sk in MEMSKEL. des_ifs.
      apply in_map_iff in H14. des. destruct x. ss. clarify. bsimpl. des.
      apply incl_filter in H0. rewrite forallb_forall in Heq3.
      hexploit Heq3; et. i. ss. destruct Pos.eq_dec; clarify. }
    { set (update _ _ _) as init_pstate. econs; et.
      { instantiate (1:=get_ce clight_prog). unfold get_ce. ss. econs. split; i.
        - apply alist_find_some_iff; et. rewrite CoqlibC.NoDup_norepet. apply Maps.PTree.elements_keys_norepet.
        - eapply alist_find_some; et. }
      { instantiate (1:= init_pstate). unfold init_pstate. unfold update. ss. }
      { ii. hexploit compile_sk_incl; et. i.
        set (ModSemL.fnsems _). eassert (a = (ModSemL.fnsems (MemSem sk_mem)) ++ _) by ss.
        rewrite H19. rewrite alist_find_app_o.
        assert (alist_find s (ModSemL.fnsems (MemSem sk_mem)) = None).
        { destruct (alist_find s) eqn:?; et.
          apply alist_find_some in Heqo.
          unfold compile, get_sk in COMP. des_ifs.
          bsimpl. des. rewrite forallb_forall in Heq3. hexploit Heq3; et. i.
          Local Opaque in_dec. ss. exfalso. destruct in_dec; clarify.
          apply n. des; clarify; ss; tauto. }
        rewrite H20. move H14 at bottom. set (List.map _ _).
        assert (alist_find s l <> None).
        { destruct (alist_find s l) eqn:?; clarify.
          clear a H19. eapply alist_find_none in Heqo. exfalso. apply Heqo.
          unfold l. rewrite in_map_iff. set (sort _).
          eexists (s, cfunU (decomp_func a (get_ce clight_prog) f)). split; et.
          generalize Sk.le_canon_rev. i. clear H20.
          ss. apply H19 in H14. unfold Sk.add in H14.
          ss. apply in_app in H14. des.
          { unfold mem_skel in MEMSKEL.
            des_ifs. rewrite in_map_iff in H14. des. destruct x; ss. clarify.
            apply filter_In in H20. des.
            unfold compile, get_sk in COMP. des_ifs.
            bsimpl. des. rewrite forallb_forall in Heq4. hexploit Heq4; et. i.
            destruct in_dec; clarify. ss. destruct in_dec; clarify. ss. exfalso. tauto. }
          unfold compile, get_sk in COMP. des_ifs. ss.
          clearbody a. clear - H14.
          induction (List.map (map_fst string_of_ident) (List.filter def_filter (prog_defs clight_prog))); i; ss.
          des. { clarify. ss. et. } des_ifs; et. ss. et. }
        destruct (alist_find s l) eqn:?; clarify.
        unfold l in Heqo. rewrite alist_find_map_snd in Heqo. uo. des_ifs.
        hexploit in_tgt_prog_defs_decomp; et. i. des. clarify.
        replace f0 with f. { eexists. f_equal. extensionalities. des_ifs. }
        clear -H23 H18 COMP.
        assert (alist_find (ident_of_string s) (prog_defs clight_prog) = Some (Gfun (Internal f))); clarify.
        apply alist_find_some_iff; et. unfold compile, get_sk in COMP. des_ifs. destruct list_norepet_dec; clarify.
        apply CoqlibC.NoDup_norepet. et. }
      { econs; et. }
      unfold itree_of_stmt, itree_stop, Es_to_eventE, kstop_itree, itree_of_cont_pop.
      unfold sk_init. ss. sim_redE. apply bind_extk. i.
      repeat (des_ifs; progress (sim_redE; grind)). }
  Qed.


  Theorem single_compile_program_improves
          clight_prog md sk_mem mn
          (COMP: compile clight_prog mn = Errors.OK md)
          (MEMSKEL: mem_skel clight_prog = Errors.OK sk_mem)
    :
      <<IMPROVES: improves2_program (clightp_sem sk_mem md) (semantics3 clight_prog)>>.
  Proof.
    red. unfold improves2_program. i. inv BEH; et.
    { hexploit single_compile_behavior_improves.
      { et. } { et. } { reflexivity. } { et. }
      inv H2. unfold improves2, clightp_initial_state.
      i. eapply H. et. }

    (* initiall wrong case, for us only when main is not found *)
    exists (Tr.ub). split; red; eauto.
    2:{ pfold. econs 4; eauto.
        - ss.
        - unfold Behaviors.behavior_prefix. exists (Behaviors.Goes_wrong Events.E0). ss. }
    ss. unfold ModSemL.initial_itr.
    destruct ModL.wf_bool.
    2:{ unfold triggerUB. grind. pfold. econs 6; ss; et.
        unfold Beh.inter. ss. i. apply ModSemL.step_trigger_take_iff in STEP.
        des. clarify. }
    red. grind. unfold ITree.map; ss.
    unfold unwrapU. des_ifs.
    (* main do not exists, ub *)
    2:{ sim_red. unfold triggerUB. grind. pfold. econs 6; ss. grind. ss. apply ModSemL.step_trigger_take_iff in STEP. des. clarify. }
    (* found main, contradiction *)
    exfalso.
    rewrite alist_find_map_snd in Heq10. uo; des_ifs; ss.
    hexploit in_tgt_prog_defs_decomp; et. i. des. clarify.
    hexploit in_tgt_prog_main; et. i. rewrite <- H in *.
    hexploit compile_init_mem_success; et. i. des.
    change (prog_defs clight_prog) with (AST.prog_defs (program_of_program clight_prog)) in H1.
    dup H1. apply alist_find_some in H1. hexploit Genv.find_symbol_exists; et.
    i. des. hexploit tgt_genv_match_symb_def_by_blk; et.
    i. apply (H0 (Callstate (Internal f) [] Kstop tm)).
    econs; et. { unfold Genv.find_funct_ptr. des_ifs. }
    clear - COMP H1 H0. unfold compile, get_sk in COMP. des_ifs.
    bsimpl. des. rewrite forallb_forall in Heq3. apply Heq3 in H1.
    unfold call_ban in H1. bsimpl. des. clear H1. unfold main_type in H2.
    des_ifs. destruct type_eq; clarify.
  Qed.

End PROOFSINGLE.
