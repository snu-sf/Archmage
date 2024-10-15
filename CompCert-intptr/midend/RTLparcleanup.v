Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import PointerOp Simulation RTLparD sflib.
Require Import Smallstep.
Require Import Dom.
Require Import Op.
Require Import SSA.
Require Import SSAutils.
Require Import Utils.
Require Import CSSA.
Require Import RTLpar.
Require Import Kildall.
Require Import KildallComp.
Require Import DLib.
Require Import Events.
Require Import CSSAutils.
Require Import Classical.
From Paco Require Import paco.

Unset Allow StrictProp.

(** ** Functions to remove redundants copies in parallel copy blocks *)

Fixpoint remove_redundant_copies visited parcb :=
  match parcb with
  | nil => nil
  | Iparcopy src dst :: parcb' =>
      if SSARegSet.mem dst visited then
        remove_redundant_copies visited parcb'
      else
        Iparcopy src dst ::
          remove_redundant_copies (SSARegSet.add dst visited) parcb'
  end.

Definition parcopycode_dstcleanup (parcode : parcopycode) :=
  PTree.map1 (remove_redundant_copies SSARegSet.empty) parcode.

Lemma remove_redundant_copies_visited_correct :
  forall parcb visited parcb' src dst,
  remove_redundant_copies visited parcb = parcb' ->
  In (Iparcopy src dst) parcb' ->
  ~ SSARegSet.In dst visited.
Proof.
  induction parcb; intros.
  go.
  simpl in *. flatten H.
  go.
  rewrite <- H in H0.
  inv H0.
  + assert(EQ: r0 = dst) by congruence. rewrite EQ in *.
    unfold not; intros.
    exploit SSARegSet.mem_1; eauto; intros.
    congruence.
  + assert(~ SSARegSet.In dst (reg_use r0 visited)).
    eapply IHparcb; eauto.
    unfold not; intros.   
    apply H.
    unfold reg_use.
    apply SSARegSet.MF.add_2. auto.
Qed.

Lemma remove_redundant_copies_correct_aux :
  forall parcb visited parcb',
  remove_redundant_copies visited parcb = parcb' ->
  NoDup (map parc_dst parcb').
Proof.
  induction parcb; intros.
  go.
  simpl in *. flatten H.
  go.
  rewrite <- H. simpl. constructor.
  + unfold not; intros.
    exploit in_parcb_dst_exists_src; eauto; intros Hexists.
    destruct Hexists as [src Hin].
    exploit remove_redundant_copies_visited_correct; eauto.
    apply SSARegSet.add_1. auto.
  + go.
Qed.

Lemma remove_redundant_copies_correct :
  forall parcb parcb',
  remove_redundant_copies SSARegSet.empty parcb = parcb' ->
  NoDup (map parc_dst parcb').
Proof.
  intros.
  eapply remove_redundant_copies_correct_aux; eauto.
Qed.

Lemma store_purged_parcb_aux :
  forall parcb parcb' rs rs' r visited,
  remove_redundant_copies visited parcb = parcb' ->
  (forall r', rs !! r' = rs' !! r') ->
  ~ SSARegSet.In r visited ->
  (parcopy_store parcb rs) !! r =
    (parcopy_store parcb' rs') !! r.
Proof.
  induction parcb; intros. go.  
  simpl in *. flatten H.
  + rewrite PMap.gso. go.
    unfold not; intros Heq. rewrite Heq in *.
    contradict H1.
    apply SSARegSet.mem_2; auto.
  + rewrite <- H. simpl.
    case_eq(peq r r1); intros.
    rewrite e. repeat rewrite PMap.gss. auto.
    repeat rewrite PMap.gso.
    eapply IHparcb; eauto.
    unfold not; intros Hin.
    contradict H1.
    eapply SSARegSet.add_3; eauto.
    destruct r; destruct r1; simpl in *; go.
    unfold not; intros. destruct H1. go.
Qed.

Lemma store_purged_parcb :
  forall parcb parcb' rs rs' r,
  remove_redundant_copies SSARegSet.empty parcb = parcb' ->
  (forall r', rs !! r' = rs' !! r') ->
  (parcopy_store parcb rs) !! r =
    (parcopy_store parcb' rs') !! r.
Proof.
  intros.
  eapply store_purged_parcb_aux; eauto.
  unfold not; intros. inv H1.
Qed.

Lemma store_purged_parcbparcb' :
  forall parcb' parcb parcb0 parcb'0 rs rs' r,
  remove_redundant_copies SSARegSet.empty parcb = parcb0 ->
  remove_redundant_copies SSARegSet.empty parcb' = parcb'0 ->
  (forall r', rs !! r' = rs' !! r') ->
  (parcopy_store parcb'
    (parcopy_store parcb rs)) !! r =
    (parcopy_store parcb'0 
    (parcopy_store parcb0 rs')) !! r.
Proof.
  intros.
  apply store_purged_parcb; eauto.
  intros.
  apply store_purged_parcb; eauto.
Qed.

(** ** The transformation *)

Definition transl_function (f : RTLpar.function) :=
    Errors.OK
      (RTLpar.mkfunction
        f.(fn_sig)
        f.(fn_params)
        f.(fn_stacksize)
        f.(fn_code)
        (parcopycode_dstcleanup f.(fn_parcopycode))
        f.(fn_entrypoint)).

Definition transl_fundef (f: RTLpar.fundef) : res RTLpar.fundef :=
  transf_partial_fundef transl_function f.

Definition transl_program (p: RTLpar.program) : Errors.res RTLpar.program :=
  transform_partial_program transl_fundef p.

Section MILL.

  Lemma remove_redundant_copies_ok:
    forall parcb,
      NoDup (map parc_dst (remove_redundant_copies SSARegSet.empty parcb)).
  Proof.
    intros.
    eapply remove_redundant_copies_correct; eauto.
  Qed.

  Lemma NoDup_list_norepet : forall (A: Type) (l:list A), NoDup l -> list_norepet l.
  Proof.
    induction 1; go. 
  Qed.  

  Lemma map_marc_dst_dests_parcb_to_moves : forall l,
      (Parmov.dests _ (parcb_to_moves l)) = 
      (map parc_dst l).
  Proof.
    unfold parcb_to_moves, Parmov.dests.
    induction l ; go.
    simpl; flatten; subst; simpl; congruence.
  Qed.

  Lemma is_mill_function : forall f tf, 
      transl_function f = Errors.OK tf -> 
      mill_function tf. 
  Proof.
    intros. 
    intros pc parcb Hparcb.
    unfold transl_function in *; inv H; simpl in *.
    unfold parcopycode_dstcleanup in *.
    rewrite PTree.gmap1 in *.
    unfold option_map in *.
    flatten Hparcb.
    eapply NoDup_list_norepet; eauto.
    rewrite map_marc_dst_dests_parcb_to_moves. 
    apply remove_redundant_copies_ok; auto.
  Qed.

  Opaque transl_function.
      
  Lemma is_mill_fundef : forall f tf, 
      transl_fundef f = Errors.OK tf -> 
      mill_fundef tf. 
  Proof.
    intros. 
    destruct f; monadInv H.
    - constructor.
      eapply is_mill_function ; eauto.
    - econstructor. 
  Qed.

End MILL.

Require Import Linking.
Require Import Registers.

Section PRESERVATION.

  Definition match_prog (p: RTLpar.program) (tp: RTLpar.program) :=
    match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

  Lemma transf_program_match:
    forall p tp, transl_program p = OK tp -> match_prog p tp.
  Proof.
    intros. apply match_transform_partial_program; auto.
  Qed.

  Section CORRECTNESS.

    Variable prog: RTLpar.program.
    Variable tprog: RTLpar.program.
    Hypothesis TRANSF_PROG: match_prog prog tprog.

    Let ge := Genv.globalenv prog.
    Let tge := Genv.globalenv tprog.

    Let sem := RTLpar.semantics prog.
    Let tsem := RTLpar.semantics tprog.

    Theorem is_mill_program : forall p tp,
        match_prog p tp ->
        mill_program tp.
    Proof.
      clear.
      intros.
      red. intros.
      inv H. 
      intuition. 
      revert H1 H0. clear.
      generalize (prog_defs tp).
      induction 1; intros.
      - inv H0.
      - inv H0.
        + clear H1 IHlist_forall2.
          inv H. inv H1.
          exploit is_mill_fundef ; eauto.
        + eapply IHlist_forall2; eauto.
    Qed.

    Inductive match_stackframes :
      list RTLpar.stackframe -> list RTLpar.stackframe -> Prop :=
    | match_stackframes_nil: match_stackframes nil nil
    | match_stackframes_cons:
        forall res f sp pc rs rs' s tf ts
               (STACK : match_stackframes s ts )
               (MREG: forall r, rs !! r = rs' !! r)
               (SPEC: transl_function f = Errors.OK tf),
          match_stackframes
            (Stackframe res f sp pc rs :: s)
            (RTLpar.Stackframe res tf sp pc rs' :: ts).

    Variant match_states: RTLpar.state -> RTLpar.state -> Prop :=
    | match_states_intro:
        forall s ts sp pc rs rs' m f tf
               (SPEC: transl_function f = Errors.OK tf)
               (STACK: match_stackframes s ts)
               (MREG: forall r, rs !! r = rs' !! r),
          match_states
            (State s f sp pc rs m)
            (RTLpar.State ts tf sp pc rs' m)
    | match_states_call:
        forall s ts f tf args m
               (SPEC: transl_fundef f = Errors.OK tf)
               (STACK: match_stackframes s ts),
          match_states
            (Callstate s f args m)
            (RTLpar.Callstate ts tf args m)
    | match_states_return:
        forall s ts v m
               (STACK: match_stackframes s ts ),
          match_states
            (Returnstate s v m)
            (RTLpar.Returnstate ts v m).
    
    Ltac dogo SPEC :=
      unfold transl_function in SPEC; go.

    Lemma registers_equal :
      forall args (rs rs' : SSA.regset),
        (forall r, rs !! r = rs' !! r) ->
        rs ## args = rs' ## args.
    Proof.
      induction args; go.
      simpl; intros.
      rewrite H.
      erewrite IHargs; eauto.
    Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
    eapply Genv.find_symbol_transf_partial; eauto.
Qed.

Lemma functions_translated:
  forall (v: val) (f: RTLpar.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf
    /\ transl_fundef f = Errors.OK tf.
Proof.
  eapply Genv.find_funct_transf_partial; eauto. 
Qed.

Lemma function_ptr_translated:
  forall (b: Values.block) (f: RTLpar.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf
    /\ transl_fundef f = Errors.OK tf.
Proof.
  eapply Genv.find_funct_ptr_transf_partial ; eauto. 
Qed.

Lemma spec_ros_r_find_function:
  forall rs rs' f r m,
  (forall r, rs !! r = rs' !! r) ->
  RTLpar.find_function ge (ros_to_vos m (inl _ r) rs) rs = Some f ->
  exists tf,
    RTLpar.find_function tge (ros_to_vos m (inl _ r) rs') rs' = Some tf
  /\ transl_fundef f = Errors.OK tf.
Proof.
  intros. simpl in H0. des_ifs.
  - erewrite H in Heq. ss. des_ifs. eapply functions_translated; eauto. ss. des_ifs.
  - erewrite H in Heq. ss. des_ifs. eapply functions_translated; eauto.
Qed.

Lemma stacksize_preserved:
  forall f tf,
  transl_function f = Errors.OK tf ->
  fn_stacksize f = fn_stacksize tf.
Proof.
  intros.
  unfold transl_function in H.
  flatten H; go.
Qed.

Lemma spec_ros_id_find_function:
  forall rs rs' f id m,
  RTLpar.find_function ge (ros_to_vos m (inr _ id) rs) rs = Some f ->
  exists tf,
     RTLpar.find_function tge (ros_to_vos m (inr _ id) rs') rs' = Some tf
  /\ transl_fundef f = Errors.OK tf.
Proof.
  intros.
  simpl in *.
  case_eq (Genv.find_symbol ge id) ; intros.
  rewrite H0 in H.
  rewrite symbols_preserved in * ; eauto ; rewrite H0 in *.
  exploit function_ptr_translated; eauto.
  rewrite H0 in H ; inv H.
Qed.

Lemma sig_fundef_translated:
  forall f tf,
    transl_fundef f = Errors.OK tf ->
    RTLpar.funsig tf = RTLpar.funsig f.
Proof.
  intros f tf. intros.
  case_eq f; intros.
  - rewrite H0 in H.
    simpl in *. Errors.monadInv H.
    simpl. auto.
  - rewrite H0 in H. go.
Qed.

Lemma transf_initial_states:
  forall st1, RTLpar.initial_state prog st1 ->
    exists st2, RTLpar.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated ; eauto. intros [tf [Hfind Htrans]].
  assert (MEM: (Genv.init_mem tprog) = Some m0)
    by (eapply (Genv.init_mem_transf_partial TRANSF_PROG); eauto).
  exists (RTLpar.Callstate nil tf nil m0); split.
  - econstructor; eauto.
    + replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
      symmetry; eapply match_program_main; eauto.
    + rewrite <- H3. apply sig_fundef_translated; auto.
  - eapply match_states_call  ; eauto.
    go.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> RTLpar.final_state st1 r -> RTLpar.final_state st2 r.
Proof.
  intros. inv H0. inv H. 
  inv STACK.
  constructor.
Qed.

Lemma senv_preserved:
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
Proof.
  eapply Genv.senv_transf_partial; eauto.
Qed.

Lemma join_point_preserved :
  forall f tf,
    transl_function f = Errors.OK tf ->
    forall pc, join_point pc f <-> join_point pc tf.  
Proof.
  intros f tf. intros.
  monadInv H.
  split; intros; invh join_point; go. 
Qed.

Lemma transl_step_correct:
  forall s1 t s2,
  IStep sem s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2',
  DStep tsem s1' t s2' /\ match_states s2 s2'.
Proof.
  destruct 1. generalize dependent s2. rename H into INT.
  induction 1; intros; inv MS.
  {
    (* inop without block *)
    exists (State ts tf sp pc' rs' m).
    split; auto.
    DStep_tac. dogo SPEC; do 2 (ss; clarify).
    econstructor 1 ; eauto.
    dogo SPEC; eauto.
    intro Hcont; eelim H0; eapply join_point_preserved; eauto.
    dogo SPEC. 
  }
  {
    (* inop with block *)
    exists (State ts tf sp pc'
      (parcopy_store (remove_redundant_copies SSARegSet.empty parcb')
      (parcopy_store (remove_redundant_copies SSARegSet.empty parcb)
        rs')) m).
    split; auto.
    DStep_tac. dogo SPEC; do 2 (ss; clarify).
    eapply RTLpar.exec_Inop_jp; eauto.
    dogo SPEC. 
    { rewrite <- join_point_preserved; eauto. }
    {
      unfold transl_function in SPEC.
      
      flatten SPEC; simpl.
      unfold parcopycode_dstcleanup.
      rewrite PTree.gmap1.
      unfold option_map.
      flatten.
      assert(Hl: (fn_parcopycode f) ! pc = Some l). auto.
      assert(Hlparcb: l = parcb). congruence. go.
      assert((fn_parcopycode f) ! pc = None). auto. congruence.
    }
    {
      unfold transl_function in SPEC.
      flatten SPEC; simpl.
      unfold parcopycode_dstcleanup.
      rewrite PTree.gmap1.
      unfold option_map.
      flatten.
      assert(Hl: (fn_parcopycode f) ! pc' = Some l). auto.
      assert(Hlparcb: l = parcb'). congruence. go.
      assert((fn_parcopycode f) ! pc' = None). auto. congruence.
    }
    dogo SPEC. dogo SPEC.
    constructor; go.
    intros.
    apply store_purged_parcbparcb'; auto.
  }
  { (* Iop *)
    exists (RTLpar.State ts tf sp pc' (rs' # res <- v) m).
    split; auto.
    DStep_tac. dogo SPEC; do 2 (ss; clarify).
    eapply RTLpar.exec_Iop; eauto.
    dogo SPEC.
    erewrite <- registers_equal; eauto.
    erewrite <- eval_operation_wrapper_preserved; eauto.
    symmetry.
    eapply symbols_preserved.
    constructor; go.
    intros.
    case_eq(peq res r); intros.
    + rewrite e.
      repeat rewrite PMap.gss; auto.
    + repeat rewrite PMap.gso; auto.
  }
  { (* Iload *)
    exists (RTLpar.State ts tf sp pc' (rs' # dst <- v) m).
    split; auto.
    - DStep_tac. dogo SPEC; do 2 (ss; clarify).
      eapply RTLpar.exec_Iload; eauto.
      dogo SPEC.
      erewrite <- registers_equal; eauto;
      try (erewrite <- eval_addressing_preserved; eauto);
      try (symmetry);
      try (eapply symbols_preserved).
    - constructor; go.
      intros.
      case_eq(peq dst r); intros.
      + rewrite e.
        repeat rewrite PMap.gss; auto.
      + repeat rewrite PMap.gso; auto.
  }
  { (* Istore *)
    exists (RTLpar.State ts tf sp pc' rs' m').
    split; auto.
    DStep_tac. dogo SPEC; do 2 (ss; clarify).
    eapply RTLpar.exec_Istore; eauto.
    dogo SPEC.
    erewrite <- registers_equal; eauto;
      try (erewrite <- eval_addressing_preserved; eauto);
      try (symmetry);
      try (eapply symbols_preserved).
    go.
    constructor; go.
  }
  { (* Icall *)
    destruct ros.
    + assert(Htfd: exists tfd,
        RTLpar.find_function tge (ros_to_vos m (inl _ r) rs') rs' = Some tfd
        /\ transl_fundef fd = Errors.OK tfd).
      eapply spec_ros_r_find_function; eauto.
      destruct Htfd as [tfd Htfd].
      exists (RTLpar.Callstate
        (RTLpar.Stackframe res tf sp pc' rs' :: ts)
        tfd (rs' ## args) m).
      split; auto.
      DStep_tac; try by (dogo SPEC; do 2 (ss; clarify)).
      eapply RTLpar.exec_Icall; eauto.
      rewrite sig_fundef_translated with (f := fd); go.
      dogo SPEC. tauto. tauto.
      erewrite registers_equal; eauto.
      econstructor; go. tauto.
    + assert(Htfd: exists tfd,
        RTLpar.find_function tge (ros_to_vos m (inr i) rs') rs' = Some tfd
        /\ transl_fundef fd = Errors.OK tfd).
      eapply spec_ros_id_find_function; eauto.
      destruct Htfd as [tfd Htfd].
      exists (RTLpar.Callstate
        (RTLpar.Stackframe res tf sp pc' rs' :: ts)
        tfd (rs' ## args) m).
      split; auto.
      DStep_tac. dogo SPEC; do 2 (ss; clarify). dogo SPEC; do 2 (ss; clarify).
      eapply RTLpar.exec_Icall; eauto.
      rewrite sig_fundef_translated with (f := fd); go.
      dogo SPEC. tauto. tauto.
      erewrite registers_equal; eauto.
      econstructor; go. tauto.
  }
  { (* Itailcall *)
    destruct ros.
    + assert(Htfd: exists tfd,
        RTLpar.find_function tge (ros_to_vos m (inl _ r) rs') rs' = Some tfd
        /\ transl_fundef fd = Errors.OK tfd).
      eapply spec_ros_r_find_function; eauto.
      destruct Htfd as [tfd Htfd].
      exists (RTLpar.Callstate ts tfd (rs' ## args) m').
      split; auto.
      DStep_tac; try by (dogo SPEC; do 2 (ss; clarify)).
      eapply RTLpar.exec_Itailcall; eauto.
      rewrite sig_fundef_translated with (f := fd); go.
      dogo SPEC. tauto. tauto.
      rewrite <- stacksize_preserved with (f := f); auto.
      erewrite registers_equal; eauto.
      econstructor; go. tauto.
    + assert(Htfd: exists tfd,
        RTLpar.find_function tge (ros_to_vos m (inr i) rs') rs' = Some tfd
        /\ transl_fundef fd = Errors.OK tfd).
      eapply spec_ros_id_find_function; eauto.
      destruct Htfd as [tfd Htfd].
      exists (RTLpar.Callstate ts tfd (rs' ## args) m').
      split; auto.
      DStep_tac. dogo SPEC; do 2 (ss; clarify). dogo SPEC; do 2 (ss; clarify).
      eapply RTLpar.exec_Itailcall; eauto.
      rewrite sig_fundef_translated with (f := fd); go.
      dogo SPEC. tauto. tauto.
      rewrite <- stacksize_preserved with (f := f); auto.
      erewrite registers_equal; eauto.
      econstructor; go. tauto.
  }
  { (* Ibuiltin *)
    exists (RTLpar.State ts tf sp pc' (regmap_setres res vres rs') m').
    split; auto.
    DStep_tac. dogo SPEC; do 2 (ss; clarify).
    unfold is_internal in INT. ss. des_ifs.
    eapply RTLpar.exec_Ibuiltin with (vargs := vargs); eauto.
    dogo SPEC.
    - eapply eval_builtin_args_preserved with (ge1:= ge); eauto.
      apply senv_preserved.
      revert H0 MREG. clear.
      induction 1 ; intros ; go.
      constructor.
      + revert H MREG. clear.
        induction 1 ; intros; go.
        rewrite MREG.
        constructor.
      + eapply IHlist_forall2; eauto.
    - eapply external_call_symbols_preserved; eauto.
      apply senv_preserved.
    - econstructor; go. intros.
      destruct res; simpl; eauto.
      case_eq(peq x r); intros.
      + rewrite e.
        repeat rewrite PMap.gss; auto.
      + repeat rewrite PMap.gso; auto. 
  }
  { (* ifso *)
    exists (RTLpar.State ts tf sp ifso rs' m).
    split; auto.
    DStep_tac. dogo SPEC; do 2 (ss; clarify).
    eapply RTLpar.exec_Icond_true; eauto.
    dogo SPEC.
    erewrite <- registers_equal; eauto.
    econstructor; go.
  }
  { (* ifnot *)
    exists (RTLpar.State ts tf sp ifnot rs' m).
    split; auto.
    DStep_tac. dogo SPEC; do 2 (ss; clarify).
    eapply RTLpar.exec_Icond_false; eauto.
    dogo SPEC.
    erewrite <- registers_equal; eauto.
    econstructor; go.
  }
  { (* ijumptable *)
    exists (RTLpar.State ts tf sp pc' rs' m).
    split; auto.
    DStep_tac. dogo SPEC; do 2 (ss; clarify).
    eapply RTLpar.exec_Ijumptable; eauto.
    dogo SPEC. go.
    econstructor; go.
  }
  { (* ireturn *)
    destruct or.
    + exists (RTLpar.Returnstate ts (regmap_optget (Some r) Vundef rs') m').
      split; auto.
      DStep_tac. dogo SPEC; do 2 (ss; clarify).
      eapply RTLpar.exec_Ireturn.
      dogo SPEC.
      rewrite <- stacksize_preserved with (f := f); auto.
      simpl. rewrite MREG. go.
    + exists (RTLpar.Returnstate ts (regmap_optget None Vundef rs') m').
      split; auto.
      DStep_tac. dogo SPEC; do 2 (ss; clarify).
      eapply RTLpar.exec_Ireturn.
      dogo SPEC.
      rewrite <- stacksize_preserved with (f := f); auto.
      go.
  }
  { (* internal *)
    destruct tf as [tf | tf].
    + exists (RTLpar.State ts tf (Vptr stk Ptrofs.zero)
        tf.(RTLpar.fn_entrypoint)
        (init_regs args (RTLpar.fn_params tf)) m').
      split; auto.
      DStep_tac.
      eapply RTLpar.exec_function_internal.
      erewrite <- stacksize_preserved; eauto.
      go. go.
    + go.
  }
  { (* external *)
    inv SPEC.
    exists (RTLpar.Returnstate ts res m').
    split; auto.
    + DStep_tac.
      eapply RTLpar.exec_function_external.
      eapply external_call_symbols_preserved; eauto.
      apply senv_preserved.
    + go.
  }
  { (* return state *)
    inv STACK.
    exists (RTLpar.State ts0 tf sp pc (rs' # res <- vres) m).
    split; auto.
    + DStep_tac. eapply RTLpar.exec_return.
    + econstructor; eauto.
      intros.
      case_eq(peq res r); intros.
      - rewrite e.
        repeat rewrite PMap.gss; auto.
      - repeat rewrite PMap.gso; auto.
  }
Qed.

Lemma match_states_bsim
      s1
      (EXT: is_external ge s1)
      s2 t s2'
      (STEPTGT: Step tsem s2 t s2')
      (MATCH: match_states s1 s2)
      (SAFESRC: safe sem s1)
  :
    (exists s1', Step sem s1 t s1' /\ match_states s1' s2').
Proof.
  assert (SEQUIV: Senv.equiv tge ge) by (symmetry; apply senv_preserved).
  unfold safe in SAFESRC. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
  { inv SAFESRC. inv MATCH. ss. }
  unfold is_external in *; des_ifs.
  (* builtin *)
  - inv STEPTGT; inv MATCH; dogo SPEC. clarify.
    exists (State stack f sp0 pc' (regmap_setres res vres rs) m').
    split; auto.
    + eapply external_call_symbols_preserved in H1; eauto.
      eapply RTLpar.exec_Ibuiltin with (vargs := vargs); eauto.
      eapply eval_builtin_args_preserved with (ge1:= tge); eauto.
      i. symmetry. eapply symbols_preserved.
      revert H0 MREG. clear.
      induction 1 ; intros ; go.
      constructor.
      * revert H MREG. clear.
        induction 1 ; intros; go.
        rewrite <- MREG.
        constructor.
      * eapply IHlist_forall2; eauto.
    + econstructor; go. intros.
      destruct res; simpl; eauto.
      case_eq(peq x r); intros.
      * rewrite e0.
        repeat rewrite PMap.gss; auto.
      * repeat rewrite PMap.gso; auto.
  (* external *)
  - inv STEPTGT; inv MATCH; dogo SPEC. clarify.
    inv SPEC.
    exists (RTLpar.Returnstate stack res m').
    split; auto.
    + eapply RTLpar.exec_function_external.
      eapply external_call_symbols_preserved; eauto.
    + go.
      Unshelve. all: eauto.
Qed.

Lemma match_states_xsim
    st_src0 st_tgt0 gmtgt
    (MATCH: match_states st_src0 st_tgt0) :
  xsim (RTLpar.semantics prog) (RTLpar.semantics tprog) gmtgt lt 0%nat st_src0 st_tgt0.
Proof.
  generalize dependent st_src0. generalize dependent st_tgt0.
  pcofix CIH. i. pfold.
  destruct (classic (is_external ge st_src0)); cycle 1.
  (* not external *)
  - left. econs. econs.
    + i. exploit transl_step_correct; eauto. i. des.
      * esplits; eauto.
        { eapply tr_rel_refl. eapply ev_rel_refl. }
        left. split.
        { eapply plus_one; eauto. }
        { eapply RTLparD.semantics_receptive_at; auto. }
    + ii. eapply final_state_determ; eauto.
      inv FINALSRC. inv MATCH. ss. inv STACK. econs.
  (* external *)
  - right. econs. i. econs.
    + i. exploit match_states_bsim; eauto. i. des.
      left. esplits; eauto.
      { eapply tr_rel_refl. eapply ev_rel_refl. }
      left. eapply plus_one. eauto.
    + i. unfold is_external in *.
      des_ifs; inv FINALTGT; inv MATCH; ss.
    (* progress *)
    + i.
      specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
      { inv SAFESRC; ss. }
      right. inv MATCH; ss; des_ifs; inv SAFESRC; unfold ge in *; clarify.
      * dogo SPEC. esplits.
        eapply exec_Ibuiltin; eauto.
        { clarify. ss. eauto. }
        { instantiate (1:=vargs).
          eapply eval_builtin_args_preserved.
          { eapply senv_preserved. }
          revert H9 MREG. clear.
          induction 1 ; intros ; go.
          constructor.
          + revert H MREG. clear.
            induction 1 ; intros; go.
            rewrite MREG.
            constructor.
          + eapply IHlist_forall2; eauto. }
        eapply external_call_symbols_preserved; eauto.
        apply senv_preserved.
      * inv SPEC.
        esplits.
        eapply RTLpar.exec_function_external.
        eapply external_call_symbols_preserved; eauto.
        apply senv_preserved.
Qed.

Lemma non_static_equiv l:
  Genv.non_static_glob (Genv.globalenv prog) l = Genv.non_static_glob (Genv.globalenv tprog) l.
Proof.
  induction l; ss.
  specialize senv_preserved. i. unfold ge, tge in H. r in H. des.
  specialize (H0 a).
  unfold Senv.public_symbol in H0. ss. rewrite <- H0.
  specialize (H a). rewrite <- H. erewrite IHl; eauto.
Qed.

Lemma same_public:
  prog_public prog = prog_public tprog.
Proof. inv TRANSF_PROG. des; eauto. Qed.

Lemma transf_initial_capture
    S1 S2 S2'
    (INITSRC: initial_state prog S1)
    (INITTGT: initial_state tprog S2)
    (MATCH: match_states S1 S2)
    (CAPTGT: glob_capture tprog S2 S2'):
  exists S1',
    glob_capture prog S1 S1'
  /\ match_states S1' S2'
  /\ gm_improves (concrete_snapshot ge S1') (concrete_snapshot tge S2').
Proof.
  specialize senv_preserved. intros SENVEQ. inv CAPTGT. ss.
  rewrite Genv.globalenv_public in CAPTURE.
  rewrite <- same_public in CAPTURE. erewrite <- non_static_equiv in CAPTURE.
  inv MATCH. inv STACK.
  esplits.
  - econs; eauto. rewrite Genv.globalenv_public. eauto.
  - econs; eauto. econs.
  - ii. unfold concrete_snapshot in *.
    inv SENVEQ. des. erewrite H1, H0. des_ifs; ss.
Qed.

Theorem transf_program_correct:
  mixed_simulation (RTLpar.semantics prog) (RTLpar.semantics tprog).
Proof.
  econs. econs.
  - apply lt_wf.
  - rr. i. exists (S a). lia.
  - econs. i. exploit transf_initial_states; eauto. i. des.
    exists st2. split.
    (* initial state *)
    + econs; eauto. eapply initial_state_determ.
    (* mixed sim *) 
    + r. ii. inversion INITSRC; subst. inversion H0; subst.
      inv STACK.
      exploit transf_initial_capture; eauto.
      i. des.
      exists 0%nat. exists S1'. esplits; eauto.
      apply match_states_xsim; auto.
  - i. apply senv_preserved.
Qed.

End CORRECTNESS.
  
End PRESERVATION.

Section WF.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF_PROG: match_prog prog tprog.
Hypothesis WF_TRANSF: wf_program prog. 

Lemma transl_function_inops : forall f tf, 
  transl_function f = Errors.OK tf -> 
  forall pc s, 
    (fn_code f) ! pc = Some (Inop s) <->
    (RTLpar.fn_code tf) ! pc = Some (Inop s).
Proof.
  unfold transl_function ; intros f tf TRANS pc s.
  flatten TRANS; simpl; go.
Qed.

Lemma transl_function_ins : forall f tf, 
  transl_function f = Errors.OK tf -> 
  forall pc, 
    (fn_code f) ! pc = (RTLpar.fn_code tf) ! pc.
Proof.
  unfold transl_function ; intros f tf TRANS pc.
  flatten TRANS; simpl ; go.
Qed.

Lemma transl_function_parcb_2 : forall f tf, 
  transl_function f = Errors.OK tf -> 
  forall pc p, 
    (RTLpar.fn_parcopycode tf) ! pc = Some p ->
    exists p, (fn_parcopycode f) ! pc = Some p. 
Proof.
  unfold transl_function ; intros f tf TRANS pc ins INS.
  flatten TRANS; simpl in *.
  unfold parcopycode_dstcleanup in *. 
  repeat rewrite PTree.gmap1 in *.
  unfold option_map in *. flatten INS ; eauto. 
Qed.

Lemma entry_point_preserved : 
  forall f tf,
  transl_function f = OK tf -> 
  RTLpar.fn_entrypoint tf = fn_entrypoint f.
Proof.
  unfold transl_function ; intros f tf TRANS.
  flatten TRANS; go.
Qed.

Lemma successors_preserved : forall f tf,
  transl_function f = Errors.OK tf -> 
  forall pc ins ins' pc', 
    (fn_code f) ! pc = Some ins ->
    (RTLpar.fn_code tf) ! pc = Some ins' ->
    (In pc' (successors_instr ins) <->
     In pc' (successors_instr ins')).
Proof.
  unfold transl_function ; intros f tf TRANS pc ins ins' pc' CODE TCODE.
  flatten TRANS; simpl in *; go.  
Qed.

Lemma successors_preserved_2 : forall f tf,
  transl_function f = Errors.OK tf -> 
  forall pc pc', In pc' (successors f) !!! pc <->
                 In pc' (RTLpar.successors tf) !!! pc.
Proof.
  intros f tf TRANS pc pc'.
  unfold successors, RTLpar.successors.
  unfold successors_list; simpl.
  repeat rewrite PTree.gmap1 in *.
  unfold option_map.
  flatten; simpl;  go ; flatten Eq0; eauto using successors_preserved ; eauto.
  - split; intuition. 
    erewrite transl_function_ins in Eq2 ; eauto. congruence.
  - split; intuition. 
    erewrite transl_function_ins in Eq2 ; eauto. congruence.
Qed.

Lemma cfg_preserved : forall f tf,
  transl_function f = Errors.OK tf -> 
  forall pc pc', cfg f pc pc' <-> RTLpar.cfg tf pc pc'.
Proof.
  intros f tf TRANS pc pc'.
  split; intros.
  - invh cfg. 
    econstructor; eauto using successors_preserved. 
    erewrite <- transl_function_ins; eauto.
  - invh RTLpar.cfg. 
    erewrite <- transl_function_ins in HCFG_ins; eauto. 
    econstructor; eauto using successors_preserved. 
Qed.

Lemma predecessors_preserved :
  forall f tf,
  wf_function f ->
  transl_function f = Errors.OK tf ->
  make_predecessors (fn_code tf) successors_instr
    = make_predecessors (fn_code f) successors_instr.
Proof.
    unfold transl_function. intros. inv H0; simpl.
    go. 
Qed.

Lemma jp_preserved_1 :
  forall f tf jp,
  wf_function f ->
  transl_function f = Errors.OK tf ->
  join_point jp f ->
  join_point jp tf.
Proof.
  intros. 
  inv H1.
  econstructor; eauto. 
  erewrite predecessors_preserved; eauto. 
Qed.

Lemma jp_preserved_2 :
  forall f tf jp,
  wf_function f ->
  transl_function f = Errors.OK tf ->
  join_point jp tf ->
  join_point jp f.
Proof.
  intros.
  inv H1.
  econstructor; eauto.
  erewrite <- predecessors_preserved; eauto.
Qed.

Lemma is_wf_function : forall f tf, 
  wf_function f ->                         
  transl_function f = Errors.OK tf -> 
  wf_function tf. 
Proof.
  intros. constructor.

  - exploit fn_entry; eauto. intros [s Hins].
    erewrite entry_point_preserved; eauto.
    rewrite transl_function_inops in Hins ; eauto. 

  - intros pc Hcont.
    invh RTLpar.cfg.
    erewrite <- transl_function_ins in HCFG_ins; eauto.
    erewrite entry_point_preserved in *; eauto.    
    eelim fn_entry_pred; go.

  - intros jp pc JP SUCC.
    erewrite <- successors_preserved_2 in SUCC; eauto.
    exploit fn_normalized ; eauto using jp_preserved_2.
    rewrite transl_function_inops; eauto.
    
  - intros pc pc' JP CFG JPCONT.
    eapply jp_preserved_2 in JP ; eauto. 
    eapply jp_preserved_2 in JPCONT ; eauto. 
    rewrite <- cfg_preserved in *; eauto.
    eelim fn_normalized_jp with (pc:= pc) (pc':= pc'); eauto.

  - intros pc pc' parcb CODE TPARC NJP.
    eapply jp_preserved_1 ; eauto.
    rewrite <- transl_function_inops in *; eauto.
    exploit transl_function_parcb_2; eauto. intros [p Hp].
    eapply fn_parcb_jp; eauto using jp_preserved_1.
    
  - intros pc PARC.
    destruct ((RTLpar.fn_parcopycode tf) ! pc) eqn: EQ; try congruence.
    exploit transl_function_parcb_2; go. intros [p' Hp'].
    exploit (fn_parcb_inop f H pc)  ; eauto; go. intros [s Hpc].
    rewrite transl_function_inops in Hpc; eauto.

  - intros pc pc' instr CODE SUCC.
    erewrite <- transl_function_ins in CODE; eauto. 
    rewrite <- successors_preserved with (ins':= instr) in SUCC; eauto.
    exploit fn_code_closed; eauto. intros [instr' CODESUCC].
    erewrite transl_function_ins in CODESUCC; eauto.
    erewrite <- transl_function_ins; eauto.
Qed.    

Theorem match_prof_wf_program : 
  wf_program tprog.
Proof.
  red. intros.
  red in  WF_TRANSF.
  inv TRANSF_PROG.
  intuition. revert H0 H WF_TRANSF.
  induction 1; intros.
  - inv H.
  - inv H1.      
    + inv H. inv H4.
      {  Opaque transl_function.
         destruct f1 ; simpl in * ; try constructor; auto.
         * monadInv H7.
           constructor. eapply is_wf_function ; eauto.
           destruct a1, g.
           exploit (WF_TRANSF (Internal f0) i); eauto.
           simpl in * ; eauto.
           left. inv H; simpl in *; auto. 
           intros. inv H1; auto.
           simpl in *. inv H.
         * monadInv H7.
           constructor.
      }
    + eapply IHlist_forall2; eauto.
Qed.
 
End WF.
