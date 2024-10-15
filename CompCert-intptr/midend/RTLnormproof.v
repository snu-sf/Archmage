(** Correctness proof for the RTL normalization phase. *)
Require Import DLib. 
Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Ordered.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import PointerOp RTLD sflib Simulation.
Require Import Smallstep.
Require Import RTL.
Require Import RTLnorm.
Require Import RTLnormspec.
Require Import Kildall.
Require Import Conventions.
Require Import Utils.
Require Import Events.
Require Import Linking.
Require Import Classical.
From Paco Require Import paco.

Unset Allow StrictProp.

Section PRESERVATION.

  Definition match_prog (p tp: RTL.program) :=
  match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

  Lemma transf_program_match:
    forall p tp, transl_program p = Errors.OK tp -> match_prog p tp.
  Proof.
    intros. apply match_transform_partial_program; auto.
  Qed.

  Section CORRECTNESS.
    
    Variable prog: RTL.program.
    Variable tprog: RTL.program.
    Hypothesis TRANSF_PROG: match_prog prog tprog.

    Let ge := Genv.globalenv prog.
    Let tge := Genv.globalenv tprog.

    Let sem := RTL.semantics prog.
    Let tsem := RTL.semantics tprog.

    Lemma symbols_preserved:
      forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
    Proof.
      eapply Genv.find_symbol_transf_partial; eauto.
    Qed.

    Lemma functions_translated:
      forall (v: val) (f: RTL.fundef),
        Genv.find_funct ge v = Some f ->
        exists tf, Genv.find_funct tge v = Some tf /\ transl_fundef f = Errors.OK tf.
    Proof.
      eapply Genv.find_funct_transf_partial; eauto.
    Qed.

    Lemma function_ptr_translated:
      forall (b: block) (f: RTL.fundef),
        Genv.find_funct_ptr ge b = Some f ->
        exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = Errors.OK tf.
    Proof.
      eapply Genv.find_funct_ptr_transf_partial ; eauto.
    Qed.

    Lemma senv_preserved:
      Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
    Proof.
      eapply Genv.senv_transf_partial; eauto.
    Qed.

    Lemma same_public:
      prog_public prog = prog_public tprog.
    Proof. inv TRANSF_PROG. des; eauto. Qed.

    Lemma sig_fundef_translated:
      forall f tf,
        transl_fundef f = Errors.OK tf ->
        funsig tf = RTL.funsig f.
    Proof.
      intros f tf. intros.
      destruct f ; simpl in *. Errors.monadInv H.
      unfold transl_function in EQ;
        flatten EQ; boolInv; go.
      inv H. auto.
    Qed.

    Lemma sig_function_translated:
      forall f tf,
        transl_function f = Errors.OK tf ->
        fn_sig tf = RTL.fn_sig f.
    Proof.
      intros f tf. destruct f; simpl; intros EQ.
      unfold transl_function in EQ;
        flatten EQ; boolInv; go.
    Qed. 

    Lemma spec_ros_r_find_function:
      forall rs f r m,
        RTL.find_function ge (ros_to_vos m (inl _ r) rs) rs = Some f ->
        exists tf,
          RTL.find_function tge (ros_to_vos m (inl _ r) rs) rs = Some tf
          /\ transl_fundef f = Errors.OK tf.
    Proof.
      intros. unfold ros_to_vos; ss. des_ifs;
      eapply functions_translated; eauto.
    Qed.

    Lemma spec_ros_id_find_function:
      forall rs f id m,
        RTL.find_function ge (ros_to_vos m (inr _ id) rs) rs = Some f ->
        exists tf,
          RTL.find_function tge (ros_to_vos m (inr _ id) rs) rs = Some tf
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

    Lemma stacksize_preserved: forall f tf, 
        transl_function f = Errors.OK tf -> 
        fn_stacksize f = fn_stacksize tf.
    Proof.
      intros f tf EQ.
      unfold transl_function in EQ;
        flatten EQ; boolInv; go.
    Qed.

    Inductive match_stackframes : list stackframe -> list stackframe -> Prop :=
    | match_stackframes_nil: match_stackframes nil nil 
    | match_stackframes_cons1: 
        forall res f sp pc rs s tf ts 
               (STACK : (match_stackframes s ts))
               (SPEC: (transl_function f = Errors.OK tf)),
          match_stackframes
            ((Stackframe res f sp pc rs) :: s)
            ((Stackframe res tf sp pc rs) :: ts)
    | match_stackframes_cons2: 
        forall res f sp pc pc' rs s tf ts aux
               (STACK : (match_stackframes s ts))
               (SPEC: (transl_function f = Errors.OK tf))
               (NORM: reach_nops (fn_code tf) pc' pc aux),
          match_stackframes
            ((Stackframe res f sp pc rs) :: s)
            ((Stackframe res tf sp pc' rs) :: ts).

    Hint Constructors match_stackframes: core.
    Set Implicit Arguments.

    Variant match_states: RTL.state -> RTL.state -> Prop :=
    | match_states_intro:
        forall s ts sp pc rs m f tf
               (SPEC: transl_function f = Errors.OK tf)
               (STACK: match_stackframes s ts),
          match_states (State s f sp pc rs m) (State ts tf sp pc rs m)
    | match_states_call:
        forall s ts f tf args m
               (SPEC: transl_fundef f = Errors.OK tf)
               (STACK: match_stackframes s ts),
          match_states (Callstate s f args m) (Callstate ts tf args m)
    | match_states_return:
        forall s ts v m 
               (STACK: match_stackframes s ts),
          match_states (Returnstate s v m) (Returnstate ts v m).
    Hint Constructors match_states: core.
    
    Lemma transf_initial_states:
      forall st1, RTL.initial_state prog st1 ->
                  exists st2, RTL.initial_state tprog st2 /\ match_states st1 st2.
    Proof.
      intros. inversion H.
      exploit function_ptr_translated ; eauto. intros [tf [Hfind Htrans]].
      econstructor; split.
      - econstructor.
        assert (MEM: (Genv.init_mem tprog) = Some m0) by (eapply (Genv.init_mem_transf_partial TRANSF_PROG); eauto).
        + apply MEM ; auto.
        + replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
          symmetry; eapply match_program_main; eauto.
        + eauto.
        + rewrite <- H3. apply sig_fundef_translated; auto.
      - eapply match_states_call  ; eauto.
    Qed.

    Lemma transf_final_states:
      forall st1 st2 r,
        match_states st1 st2 -> RTL.final_state st1 r -> RTL.final_state st2 r.
    Proof.
      intros. inv H0. inv H. 
      inv STACK.
      constructor.
    Qed.

    Create HintDb valagree.
    Hint Resolve symbols_preserved : valagree.
    Hint Resolve eval_addressing_preserved : valagree.
    Hint Resolve eval_operation_preserved : valagree.
    Hint Resolve sig_function_translated : valagree.
    Hint Resolve sig_fundef_translated : valagree.
    Hint Resolve senv_preserved : valagree.
    Hint Resolve stacksize_preserved: valagree.

    Lemma reach_nop_star :  forall ts pt regs m aux x pcx pc,
        reach_nops (fn_code x) pcx pc aux ->
        star (fun _ : genvtype tsem => DStep tsem) (globalenv tsem) (RTL.State ts x pt pcx regs m) E0 (RTL.State ts x pt pc regs m).
    Proof.
      induction aux; intros.
      - inv H.  eapply star_step. DStep_tac ; eauto ; go. go. traceEq.
      - inv H.
        exploit IHaux ; eauto. i. eapply star_left; eauto.
        DStep_tac. eapply exec_Inop; eauto. traceEq.
    Qed.

    Lemma reach_nop_star_src :  forall ts pt regs m aux x pcx pc,
        reach_nops (fn_code x) pcx pc aux ->
        star (fun _ : genvtype sem => Step sem) (globalenv sem) (RTL.State ts x pt pcx regs m) E0 (RTL.State ts x pt pc regs m).
    Proof.
      induction aux; intros.
      - inv H.  eapply star_step.  eauto ; go. go. traceEq.
      - inv H.
        exploit IHaux ; eauto. i. eapply star_left; eauto.
        eapply exec_Inop; eauto. traceEq.
    Qed.

    Ltac allinv := 
      repeat 
        match goal with 
        | [H: value ?s = Some ?s' |- _ ] => inv H
        | [ H1:   (fn_code ?tf) ! ?pc = Some _  ,
                  H2: (fn_code ?tf) ! ?pc = Some _ |- _ ] =>
          rewrite H1 in H2; inv H2
        | [ H1:   (RTL.fn_code ?tf) ! ?pc = Some _  ,
                  H2: (RTL.fn_code ?tf) ! ?pc = Some _ |- _ ] =>
          rewrite H1 in H2; inv H2
        | _ => idtac
        end.

    Variant ch_succ : instruction -> instruction -> Prop :=
    |cs_inop : forall s1 s2, ch_succ (Inop s1) (Inop s2)
    |cs_iop: forall s1 s2 op args dst, ch_succ (Iop op args dst s1) (Iop op args dst s2)
    |cs_iload: forall s1 s2 chunk addr args dst, ch_succ (Iload chunk addr args dst s1) (Iload chunk addr args dst s2)
    |cs_istore: forall s1 s2 chunk addr args src, ch_succ (Istore chunk addr args src s1) (Istore chunk addr args src s2)
    |cs_icall: forall s1 s2 sig fn args dst, ch_succ (Icall sig fn args dst s1) (Icall sig fn args dst s2)
    |cs_itailcall: forall sig fn args, ch_succ (Itailcall sig fn args) (Itailcall sig fn args)
    |cs_ibuiltin : forall s1 s2 ef args dst, ch_succ (Ibuiltin ef args dst s1) (Ibuiltin ef args dst s2)
    |cs_icond : forall cond args i1 i2 n1 n2, ch_succ (Icond cond args i1 n1) (Icond cond args i2 n2)
    |cs_ijump: forall arg tbl1 tbl2, List.length tbl1 = List.length tbl2 -> ch_succ (Ijumptable arg tbl1) (Ijumptable arg tbl2)
    |cs_iret : forall ret, ch_succ (Ireturn ret) (Ireturn ret).

    Lemma ch_succ_dec_spec : forall i1 i2, 
        ch_succ_dec i1 i2 = true -> ch_succ i1 i2.
    Proof.
      destruct i1, i2 ; simpl ; 
        intros; try boolInv ; go.
    Qed.

Ltac normalized := 
  match goal with 
    | id: context[norm _ _ _ ] |- _ =>
    (exploit id ; eauto; intros);
    (invh norm; allinv); 
    (exploit ch_succ_dec_spec ; eauto ; intros ; invh ch_succ)
  end.

Ltac succ n s := 
  match goal with 
    | id : forall (k : nat) (succ succ' : node), _ |- _ =>
       specialize (id n); simpl in *;
       exploit id; eauto; intros [HC1 | [nops [HC2 HC3]]]; subst;
       exists s ; (split ; go ; (econstructor; try DStep_tac; eauto using reach_nop_star; go))
  end.

(* Ltac succ n s :=  *)
(*   match goal with  *)
(*     | id : forall (k : nat) (succ succ' : node), _ |- _ => *)
(*        specialize (id n); simpl in *; *)
(*        exploit id; eauto; intros [HC1 | [nops HC2]]; subst; *)
(*        exists s ; (split ; go ; (econstructor; try DStep_tac; eauto using reach_nop_star; go)) *)
(*   end. *)

(* try DStep_tac ; *)

Lemma transl_step_correct:
  forall s1 t s2,
    IStep sem s1 t s2 ->
    forall s1' (MS: match_states s1 s1'),
    exists s2', DPlus tsem s1' t s2' /\ match_states s2 s2'.
Proof.
  destruct 1. generalize dependent s2. rename H into INT.
  induction 1; intros; inv MS; auto; 
  match goal with 
    | [H : transl_fundef (Internal ?f) = _ |- _ ] => idtac
    | [H : transl_fundef (External ?f) = _ |- _ ] => idtac
    | [  |- context [Returnstate ?ts ?vres ?m]] => idtac
    | _ => 
      ( (exploit transl_function_spec_ok ; eauto; intros))
  end ;
  match goal with 
    | [SPEC: transl_function_spec ?f ?tf |- _ ] => inv SPEC
    | _ => idtac
  end.
  
  - (* inop *)
    normalized.
    succ O (RTL.State ts tf sp pc' rs m).
    
  - (* iop *)
    normalized. 
    succ O (RTL.State ts tf sp pc' (rs#res <- v) m).
    + econstructor 2 ; eauto.
      rewrite <- H0 ; eauto with valagree.
      eapply eval_operation_wrapper_preserved. eapply senv_preserved.
    + auto.
    + econstructor 2 ; eauto.
      rewrite <- H0 ; eauto with valagree.
      eapply eval_operation_wrapper_preserved. eapply senv_preserved.
    + auto.

  - (* iload *)
    normalized. 
    succ O (RTL.State ts tf sp pc' (rs#dst <- v) m);
      first [econstructor 3; eauto;
             rewrite <- H0 ; eauto with valagree
            |auto
            |econstructor 3 ; eauto;
             rewrite <- H0 ; eauto with valagree
            | auto].
    
  - (* istore *)
    normalized. 
    succ O (RTL.State ts tf sp pc' rs m');
    first [ econstructor 4 ; eauto;
            rewrite <- H0 ; eauto with valagree
          | auto
          | econstructor 4 ; eauto;
            rewrite <- H0 ; eauto with valagree
          | auto].
  
  - (* icall *)
    normalized.
    destruct ros; 
      [ exploit spec_ros_r_find_function ; eauto 
      | exploit spec_ros_id_find_function ; eauto] ; 
      (intros [tf' [Hfind OKtf']]).
    + specialize (H5 O) ; simpl in *.
      exploit H5 ; eauto ; intros [HC1 | [aux' [HC2 HC3]]]; subst.
      * exists (Callstate (Stackframe res tf sp pc' rs :: ts) tf' rs ## args m); split;
        [   (eapply plus_one ; eauto);
          (DStep_tac; eapply exec_Icall  ; eauto); 
          (eauto with valagree)
          |
          (constructor ; auto);
            (econstructor ; eauto);
            (replace (fn_sig tf) with (fn_sig f); eauto); 
            (symmetry ; eauto with valagree)].
      * exists (Callstate (Stackframe res tf sp s2 rs :: ts) tf' rs ## args m); split.
        { (eapply plus_one ; eauto);
          (DStep_tac; eapply exec_Icall  ; eauto); 
          (eauto with valagree). }
        { (constructor ; auto);
          (econstructor ; eauto);
          (replace (fn_sig tf) with (fn_sig f); eauto); 
          (symmetry ; eauto with valagree). } 

    + specialize (H5 O) ; simpl in *.
      exploit H5 ; eauto ; intros [HC1 | [aux' [HC2 HC3]]]; subst.
      * exists (Callstate (Stackframe res tf sp pc' rs :: ts) tf' rs ## args m); split;
        [   (eapply plus_one ; eauto);
          (DStep_tac; eapply exec_Icall  ; eauto); 
          (eauto with valagree)
          |
          (constructor ; auto);
            (econstructor ; eauto);
            (replace (fn_sig tf) with (fn_sig f); eauto); 
            (symmetry ; eauto with valagree)]. 
      * exists (Callstate (Stackframe res tf sp s2 rs :: ts) tf' rs ## args m); split.
        { (eapply plus_one ; eauto);
          (DStep_tac; eapply exec_Icall  ; eauto); 
          (eauto with valagree). }
        { (constructor ; auto);
          (econstructor ; eauto);
          (replace (fn_sig tf) with (fn_sig f); eauto); 
          (symmetry ; eauto with valagree). 
        }

  - (* itailcall *)
    normalized. 
    destruct ros;
    [exploit spec_ros_r_find_function ; eauto
      | exploit spec_ros_id_find_function ; eauto];
    (intros EQ; destruct EQ as [tf' [Hfind OKtf']]);
    (exploit (sig_function_translated f tf) ; eauto ; intros);
    
    ((exists (Callstate ts tf' rs##args m');  split);
      [  (eapply plus_one ; eauto); 
        (DStep_tac; eapply exec_Itailcall ; eauto with valagree);
        (replace (fn_stacksize tf) with (fn_stacksize f); eauto with valagree)
        | ( (constructor; auto);
          (eapply match_stackframes_change_sig ;eauto with valagree))]);
    eapply tailcall_ok ; eauto.
    
  - (* ibuiltin *)
    normalized.
    ss.
    succ O (RTL.State ts tf sp pc' (regmap_setres res vres rs) m').
    { unfold is_internal in *. ss. des_ifs. }
    3:{ unfold is_internal in *. ss. des_ifs. }
    + econstructor; eauto.
      eapply eval_builtin_args_preserved with (ge1:= ge); eauto with valagree.
      eapply external_call_symbols_preserved; eauto with valagree.
    + rewrite E0_right; eauto. 
    + econstructor; eauto.
      eapply eval_builtin_args_preserved with (ge1:= ge); eauto with valagree.
      eapply external_call_symbols_preserved; eauto with valagree.
    + rewrite E0_right; eauto. 
    
  - (* ifso *)
    destruct b.
    + normalized.
      succ O (RTL.State ts tf sp ifso rs m).
    + normalized.
      succ (S 0) (RTL.State ts tf sp ifnot rs m).

  - (* ijump *)
    normalized. 
    exploit @list_nth_z_nth_error ; eauto; intros.  
    exploit @nth_error_some_same_length; eauto ; intros [e Hnth].
    (specialize (H6 (Z.to_nat (Int.unsigned n))); simpl in *).
    exploit H6; eauto; intros [HC1 | [nops [HC2 HC3]]]; subst.
    + exists (RTL.State ts tf sp pc' rs m); split ; eauto. 
      econstructor; eauto.
      DStep_tac.
      eapply exec_Ijumptable ; eauto.
      exploit @nth_error_list_nth_z ; eauto.
      eapply @list_nth_z_ge0 ; eauto.
      go. 
      auto. 
    + exists (RTL.State ts tf sp pc' rs m); split ; eauto. 
      econstructor; eauto.
      DStep_tac.
      eapply exec_Ijumptable ; eauto.
      exploit @nth_error_list_nth_z ; eauto.
      eapply @list_nth_z_ge0 ; eauto.
      eauto using reach_nop_star. 
      auto. 
  
  - (* ireturn *)
    (exploit transl_function_spec_ok ; eauto; intros SPEC').
    inv SPEC'.
    assert (Hpc := NORM pc). 
    exploit Hpc ; eauto ; intros Hnorm. 
    inv Hnorm; allinv; try congruence. 
    exploit ch_succ_dec_spec; eauto ; intros ; invh ch_succ.
    exists (Returnstate ts (regmap_optget or Vundef rs) m'); split ; eauto. 
    eapply plus_one ; eauto.
    DStep_tac.
    eapply exec_Ireturn ; eauto.
    rewrite <- H0 ; eauto with valagree.
    rewrite stacksize_preserved with f tf ; eauto.

  - (* internal *)
    simpl in SPEC. Errors.monadInv SPEC.
    exists (RTL.State ts x (Vptr stk Ptrofs.zero) (fn_entrypoint f)
                          (init_regs args x.(fn_params))
                          m').
    split.
    + exploit transl_function_spec_ok; eauto. intros SPEC.
      inv SPEC. destruct ENTRY as [ENTRY HLEN].
      eapply plus_left with (s2:=(RTL.State ts x (Vptr stk Ptrofs.zero) (fn_entrypoint x) 
                                            (init_regs args (fn_params x)) m')) ; eauto. 
      DStep_tac.
      eapply exec_function_internal; eauto.
      rewrite stacksize_preserved with f x in H ; auto.
      eapply reach_nop_star ; eauto.
      auto.
    + replace (RTL.fn_params f) with (fn_params x).
      econstructor ; eauto.
      unfold transl_function in EQ.
      flatten EQ; try congruence.
      auto.

  - (* external *)
    inv SPEC.
    exists (Returnstate ts res m'). split. 
    eapply plus_one ; eauto.
    DStep_tac.
    eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto with valagree.
    econstructor ; eauto.
  
  - (* return state *)
    inv STACK. 
    exists (RTL.State ts0 tf sp pc (rs# res <- vres) m).
    split. eapply plus_one ; eauto. DStep_tac. constructor ; eauto.
    constructor ; auto.
    
    exists (RTL.State ts0 tf sp pc (rs# res <- vres) m).
    split. 
    eapply plus_left with 
    (s2:= (RTL.State ts0 tf sp pc' (rs# res <- vres) m) )  ; eauto. 
    DStep_tac.
    constructor ; eauto.
    eapply reach_nop_star; eauto. 
    auto. 
    constructor ; auto.
Qed.

(* Lemma match_states_bsim *)
(*       s1 *)
(*       (EXT: is_external ge s1) *)
(*       s2 t s2' *)
(*       (STEPTGT: Step tsem s2 t s2') *)
(*       (MATCH: match_states s1 s2) *)
(*       (SAFESRC: safe sem s1) *)
(*   : *)
(*     (exists s1', Plus sem s1 t s1' /\ match_states s1' s2'). *)
(* Proof. *)
(*   assert (SEQUIV: Senv.equiv tge ge) by (symmetry; apply senv_preserved). *)
(*   unfold safe in SAFESRC. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify. *)
(*   { inv SAFESRC. inv MATCH. inv STACK. inv STEPTGT. } *)
(*   inv MATCH; ss; des_ifs; *)
(*   match goal with  *)
(*     | [H : transl_fundef (Internal ?f) = _ |- _ ] => idtac *)
(*     | [H : transl_fundef (External ?f) = _ |- _ ] => idtac *)
(*     | [  |- context [Returnstate ?ts ?vres ?m]] => idtac *)
(*     | _ =>  *)
(*       ( (exploit transl_function_spec_ok ; eauto; intros)) *)
(*   end ; *)
(*   match goal with  *)
(*     | [SPEC: transl_function_spec ?f ?tf |- _ ] => inv SPEC *)
(*     | _ => idtac *)
(*   end. *)
(*   (* builtin *) *)
(*   - normalized. *)
(*     inv STEPTGT; ss; clarify. inv SAFESRC; clarify. *)
(*     assert (vargs0 = vargs). *)
(*     { eapply eval_builtin_args_preserved in H11; [| symmetry; eapply senv_preserved]. *)
(*       eapply eval_builtin_args_determ; eauto. } *)
(*     subst.     *)
(*     exists (RTL.State s f sp n (regmap_setres b vres rs) m'). *)
(*     split. *)
(*     + exploit (H3 O); simpl in *; eauto. i. des. *)
(*       * subst. eapply plus_one. econs; eauto. *)
(*         eapply external_call_symbols_preserved; eauto with valagree. *)
(*       * econs; eauto. *)
(*         { eapply exec_Ibuiltin; eauto. } *)
(*         { exploit reach_nop_star_src; eauto. *)
(*         eapply external_call_symbols_preserved; eauto with valagree. *)
(*     + econs. *)
(*     + *)

Lemma match_states_xsim
    st_src0 st_tgt0 gmtgt n
    (MATCH: match_states st_src0 st_tgt0) :
  xsim (semantics prog) (semantics tprog) gmtgt lt n st_src0 st_tgt0.
Proof.
  generalize dependent st_src0. generalize dependent st_tgt0.
  pcofix CIH. i. pfold.
  destruct (classic (RTL.is_external ge st_src0)); cycle 1.
  (* not external *)
  - left. econs. econs.
    + i. exploit transl_step_correct; eauto. i. des. esplits.
      { eapply tr_rel_refl. eapply ev_rel_refl. }
      { left. split; eauto. eapply semantics_receptive_at; auto. }
      right. eapply CIH; eauto.
    + ii. eapply final_state_determ; eauto.
      inv FINALSRC. inv MATCH. inv STACK. econs.
  (* external *)
  - right. econs. i. econs.
    + i. assert (SEQUIV: Senv.equiv tge ge) by (symmetry; apply senv_preserved).
      unfold safe in SAFESRC. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
      { inv SAFESRC. inv MATCH. inv STACK. inv STEPTGT. }
      inv MATCH; ss; des_ifs;
        match goal with
        | [H : transl_fundef (Internal ?f) = _ |- _ ] => idtac
        | [H : transl_fundef (External ?f) = _ |- _ ] => idtac
        | [  |- context [Returnstate ?ts ?vres ?m]] => idtac
        | _ =>
            ( (exploit transl_function_spec_ok ; eauto; intros))
        end ;
        match goal with
        | [SPEC: transl_function_spec ?f ?tf |- _ ] => inv SPEC
        | _ => idtac
        end.
      (* builtin *)
      * inv SAFESRC; clarify.
        normalized. pose proof STEPTGT as STEPTGT'. inv STEPTGT; clarify.
        specialize (H4 O); simpl in *.
        exploit H4; eauto; i; des; clarify.
        { left. esplits; eauto.
          { eapply tr_rel_refl. eapply ev_rel_refl. }
          left. eapply plus_one. econs; eauto.
          eapply external_call_symbols_preserved; eauto with valagree.
          assert (vargs = vargs0).
          { exploit eval_builtin_args_determ. eapply H15.
            eapply eval_builtin_args_preserved. i; eapply symbols_preserved.
            eapply H9. i; eauto. }
          clarify. }
        { eapply (reach_nop_star ts sp rs m) in H0 as REACH. inv REACH.
          - left. esplits; eauto.
            { eapply tr_rel_refl. eapply ev_rel_refl. }
            left. eapply plus_one. econs; eauto.
            eapply external_call_symbols_preserved; eauto with valagree.
            assert (vargs = vargs0).
            { exploit eval_builtin_args_determ. eapply H15.
              eapply eval_builtin_args_preserved. i; eapply symbols_preserved.
              eapply H9. i; eauto. }
            clarify.
          - destruct aux0 as [ | nop0 [ | nop1 [ | nop2 aux2 ]]]; cycle 3.
            + ss. lia.
            + exploit Eapp_E0_inv; eauto; i; des; clarify.
              inv H0.
              left.
              eexists; eexists; exists (S n); esplits.
              { eapply tr_rel_refl. eapply ev_rel_refl. }
              left. eapply plus_one. econs; eauto.
              enough (vargs = vargs0). subst vargs; eauto using external_call_symbols_preserved.
              exploit eval_builtin_args_determ; cycle 2.
              eauto. eauto. eapply eval_builtin_args_preserved; eauto using symbols_preserved.
              left. pfold. econs 2. econs. i. econs 1. i.
              left. inv STEPTGT; clarify.
              2:{ i. inv FINALTGT. }
              2:{ right. esplits; eauto. econs; eauto. }
              esplits.
              { econs. }
              { right. esplits; eauto. eapply star_refl. }
              right. eapply CIH. econs; eauto.
            + exploit Eapp_E0_inv; eauto; i; des; clarify.
              inv H0. inv H17.
              left. eexists; exists tr'; exists (S (S n)); esplits.
              eapply tr_rel_refl; eapply ev_rel_refl.
              left. eapply plus_one. econs; eauto.
              enough (vargs = vargs0). subst vargs; eauto using external_call_symbols_preserved.
              exploit eval_builtin_args_determ; cycle 2.
              eauto. eauto. eapply eval_builtin_args_preserved; eauto using symbols_preserved.
              left. pfold. econs 2. econs. i. econs.
              { ii. inv STEPTGT; clarify. left. esplits.
                eapply tr_rel_refl; eapply ev_rel_refl. right; split.
                eapply star_refl. auto. left. pfold. econs 2. econs. i. econs.
                ii. inv STEPTGT; clarify. left. esplits.
                eapply tr_rel_refl; eapply ev_rel_refl. right; split.
                eapply star_refl. auto. right. eapply CIH; econs; eauto.
                ii. inv FINALTGT. right; esplits; eauto. econs; eauto. }
              { ii. inv FINALTGT. }
              { right; esplits; eauto. econs; eauto. }
            + exploit Eapp_E0_inv; eauto; i; des; clarify.
              inv H0. inv H17. inv H13.
              left. eexists; exists tr'; exists (S (S (S n))); esplits.
              eapply tr_rel_refl; eapply ev_rel_refl.
              left. eapply plus_one. econs; eauto.
              enough (vargs = vargs0). subst vargs; eauto using external_call_symbols_preserved.
              exploit eval_builtin_args_determ; cycle 2.
              eauto. eauto. eapply eval_builtin_args_preserved; eauto using symbols_preserved.
              left. pfold. econs 2. econs. i. econs.
              { ii. inv STEPTGT; clarify. left. esplits.
                eapply tr_rel_refl; eapply ev_rel_refl. right; split.
                eapply star_refl. auto. left. pfold. econs 2. econs. i. econs.
                ii. inv STEPTGT; clarify. left. esplits.
                eapply tr_rel_refl; eapply ev_rel_refl. right; split.
                eapply star_refl. auto. left. pfold. econs 2. econs. i. econs.
                ii. inv STEPTGT; clarify. left. esplits.
                eapply tr_rel_refl; eapply ev_rel_refl. right; split.
                eapply star_refl. auto.
                right. eapply CIH; econs; eauto.
                ii. inv FINALTGT. right; esplits; eauto. econs; eauto.
                ii. inv FINALTGT. right; esplits; eauto. econs; eauto. }
              { ii. inv FINALTGT. }
              { right; esplits; eauto. econs; eauto. } }
      (* external *)
      * left.
        inv STEPTGT; ss; clarify. inv SAFESRC; clarify.
        exists (Returnstate s res m'). esplits.
        eapply tr_rel_refl; eapply ev_rel_refl.
        { left. eapply plus_one. econs.
          eapply external_call_symbols_preserved; eauto with valagree. }
        { right. eapply CIH; eauto. }
    + i. unfold is_external in H; des_ifs; inv MATCH; inv FINALTGT.
    + assert (SEQUIV: Senv.equiv tge ge) by (symmetry; apply senv_preserved).
    
      unfold safe in SAFESRC. exploit SAFESRC; [ eapply star_refl | ]; i.

      des. { unfold is_external in H; des_ifs; inv H0. }
      inv H0; unfold is_external in H; des_ifs; inv MATCH;

      (* right; esplits; eauto. eapply exec_function_external. *)
      match goal with
      | [H : transl_fundef (Internal ?f) = _ |- _ ] => idtac
      | [H : transl_fundef (External ?f) = _ |- _ ] => idtac
      | [  |- context [Returnstate ?ts ?vres ?m]] => idtac
      | _ =>
          ( (exploit transl_function_spec_ok ; eauto; intros))
      end ;
      match goal with
      | [SPEC: transl_function_spec ?f ?tf |- _ ] => inv SPEC
      | _ => idtac
      end. normalized.

      right; esplits; eauto. eapply exec_Ibuiltin; eauto.
      eapply eval_builtin_args_preserved; cycle 1. eauto. i.
      eauto using symbols_preserved.
      eapply external_call_symbols_preserved; eauto. symmetry. eauto.

      inv SPEC. right; esplits; eauto. econs.
      eapply external_call_symbols_preserved; eauto. symmetry; eauto.
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
  - econs; eauto.
  - ii. unfold concrete_snapshot in *.
    inv SENVEQ. des. erewrite H1, H0. des_ifs; ss.
Qed.

Theorem transf_program_correct:
  mixed_simulation (RTL.semantics prog) (RTL.semantics tprog).
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
