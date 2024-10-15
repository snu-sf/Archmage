Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import CSSA.
Require Import SSA.
Require Import SSAutils.
Require Import CSSAgen.
Require Import Kildall.
Require Import Utils.
Require Import KildallComp.
Require Import DLib.
Require Import CSSAgenspec.
Require Import CSSAutils.
Require Import CSSAproof.
Require Import Classical.
Require Import Coqlib.
Require Import CSSA.
Require Import CSSAgenwf.
Unset Allow StrictProp.

Section CSSAparDefProp.

Variable tf : CSSA.function.

Inductive phi_resources (pc : node) : list reg -> Prop :=
 pr_intro: forall phib dst args ,
            forall (PHICODE: (CSSA.fn_phicode tf) ! pc = Some phib)
                   (PHI: In (Iphi args dst) phib),
              phi_resources pc (dst::args).

Lemma cssaliveout_use_def : forall r pc,
   (forall pc, use tf r pc -> def tf r pc) ->
   cssaliveout_spec tf r pc ->
   False.
Proof.
  induction 2 ; go.
Qed.

Lemma ninterlive_spec_sym: forall r1 r2, 
  ninterlive_spec tf r1 r2 ->
  ninterlive_spec tf r2 r1.
Proof.
  induction 1 ; go.
Qed.

End CSSAparDefProp.

Section transl_function_Properties.

Variable f : SSA.function.
Hypothesis WF: wf_ssa_function f.

Variable tf : CSSA.function.
Hypothesis TRANSL: transl_function f = Errors.OK tf.

Lemma STRUCT1: check_parcborparcb' tf = true.
Proof.
  unfold transl_function in *; flatten TRANSL ; boolInv ; auto.
Qed.
Hint Resolve STRUCT1: core.

Lemma NORM: normalized_jp f.
Proof.
  unfold transl_function in *; flatten TRANSL ; boolInv ; auto.
  eapply normalisation_checker_correct; eauto.
Qed.
Hint Resolve NORM: core.

Lemma use_phi_pltmaxreg_r:
  forall r pc,
  use_phicode tf r pc  ->
  Plt (get_maxreg f) r.
Proof.
  intros r pc Hphi. 
  exploit CSSAproof.transl_function_charact; eauto. intros.
  exploit transl_function_spec_ok; eauto. 
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in TRANSL.
  flatten TRANSL.
  unfold init_state in *.
  inv Hphi.
  inv SPEC; simpl in *.
  assert(Hinop: exists succ, (CSSA.fn_code (get_tf s' f)) ! pc0 = Some (Inop succ))
    by (eapply cssa_fn_inop_in_jp; go).
  simpl in Hinop.
  destruct Hinop as [succ0 Hinop].
  specialize (H2 pc0 (Inop succ0) k Hinop).
  inv H2; go.
  - rewrite exists_phib_iff_none in H1; go. go.
  - allinv.  clear Eq2 Eq1 H Hremembertrans.
    exploit index_pred_some_nth; eauto.
    unfold successors_list. rewrite H6 at 1. 
    intros. rewrite H in H7 at 1. congruence. 
  - allinv.  
    exploit equiv_phib_spec_plt_maxreg_phib'arg ; eauto.
Qed.

(* Utilitiy lemmas *)
Lemma nodups_in_preds_cssa : 
  forall l preds pc, 
    preds = make_predecessors (fn_code tf) successors_instr ->
    (fn_phicode tf) ! pc <> None ->
    preds ! pc = Some (l:list node) -> ~ In pc l -> NoDup (pc :: l).
Proof.
  intros; subst.
  erewrite instructions_preserved in H1; eauto.
  eapply nodups_in_preds ; eauto.
  eapply exists_phib_iff; eauto.
Qed.  

Lemma phi_source_use_phicode : forall pc phib args dst r,
   (fn_phicode tf) ! pc = Some phib ->
   In (Iphi args dst) phib ->
   In r args ->
   exists k, cfg tf k pc /\ use_phicode tf r k.
Proof.
  intros.
  exploit in_nth_error_some ; eauto. intros [k0 Hk0].
  exploit Hblock_nb_args; eauto. intros Heq. symmetry in Heq.
  eapply nth_error_some_same_length in Heq ; eauto.
  destruct Heq as [p Hnth].
  unfold successors_list in Hnth. flatten Hnth.
  - exploit index_pred_from_nth ; eauto.
    + eapply nodups_in_preds_cssa; go.
      intro. 
      assert (exists p, (SSA.fn_phicode f) ! pc = Some p).
      { case_eq (SSA.fn_phicode f) ! pc; intros; go.
        eelim exists_phib_iff_none with (pc:= pc) ; eauto; go. 
        intros Hif _. eelim Hif ; go.
      }        
      destruct H3 as [pb Hpb].
      erewrite NORM with (pc:= pc) in Hpb ; go.
      erewrite instructions_preserved in Eq; eauto.
    + intros. exists p. 
      split; go.
      exploit pred_is_edge; eauto. intros.
      invh is_edge; go.
  - rewrite nth_error_nil_notSome_node in Hnth; go. 
Qed.

Lemma phiresources_use_def : forall pc resources,
 phi_resources tf pc resources ->
 forall r, In r resources ->
 (forall pc, use tf r pc -> def tf r pc).
Proof.
  induction 1; intros.
  invh In.
  - (* Phi destination *)
    invh use. 
    + (* code *)
      assert (SSA.use_code f r pc0)
        by (invh use_code; erewrite instructions_preserved in H0; go).
      apply use_code_plemaxreg in H0 ; eauto.
      exploit assigned_phi_pltmaxreg_r; eauto. intro Hcont.
      eapply Pos.le_nlt in H0 ; go. 
    + (* phicode *) 
      exploit wf_cssa_extrainv_2 ; eauto. 
    + (* parcopycode *) 
      destruct (classic (join_point pc0 tf)).
      * exploit wf_cssa_extrainv_1; eauto. 
      * exploit used_parcnotjp_use_phi; eauto using join_points_preserved.
        intros. 
        apply use_phib_ple_maxreg in H1 ; eauto.
        exploit assigned_phi_pltmaxreg_r; eauto. intro Hcont.
        eapply Pos.le_nlt in H1 ; go. 
  - (* Phi source *) 
    exploit phi_source_use_phicode; eauto. intros [p [Hp Hcfg]].
    invh use. 
    + (* code *)
      assert (SSA.use_code f r pc0)
        by (invh use_code; erewrite instructions_preserved in H0; go).
      apply use_code_plemaxreg in H0 ; eauto.
      exploit use_phi_pltmaxreg_r ; go. intros.
      eapply Pos.le_nlt in H2 ; go. 
    + (* phicode *)
      exploit wf_cssa_extrainv_2; eauto. 
    + (* parcopycode *) 
      destruct (classic (join_point pc0 tf)).
      * exploit wf_cssa_extrainv_1; eauto. 
      * exploit used_parcnotjp_use_phi; eauto using join_points_preserved.
        intros. apply use_phib_ple_maxreg in H2 ; eauto.        
        exploit use_phi_pltmaxreg_r ; go. intros.
        eapply Pos.le_nlt in H2 ; go.         
Qed.

Lemma phi_resource_def : forall pc res, 
                           phi_resources tf pc res -> 
                           forall r, In r res ->
                           exists d, def tf r d.
Proof.
  induction 1; intros; invh In; go.
  exploit phi_source_use_phicode; eauto. intros [k [CFG USE]].
  eapply exists_def; go.
Qed.

Lemma unique_def_spec_def : forall x d1 d2,
  def tf x d1 ->
  def tf x d2 ->
  d1 <> d2 -> False.
Proof.
  intros.
  edestruct (p_fn_cssa f WF) as [Hssa1 Hssa2]; eauto.
  generalize (p_fn_entry f WF tf TRANSL) ; intros. destruct H2 as [succ Hentry].
  generalize (p_fn_cssa_params f WF tf TRANSL); intros Hparams.
  repeat invh def;
  repeat invh ext_params;
  try congruence ;
  try solve 
      [ exploit Hparams ; eauto; intros (HH & HH' & HH'') ; (exploit HH ; eauto)
       |exploit Hparams ; eauto; intros (HH & HH' & HH'') ; (exploit HH' ; eauto)
       |exploit Hparams ; eauto; intros (HH & HH' & HH'') ; (exploit HH'' ; eauto)
       | eelim H4; eauto
       | eelim H5; eauto
       | eelim H3; eauto
       | eelim (Hssa1 x d1 d2) ; eauto ; intuition ; eauto
      ].
Qed.

Lemma def_def_eq : forall x d1 d2,
  def tf x d1 ->
  def tf x d2 ->
  d1 = d2.
Proof.
  intros.
  destruct (peq d1 d2) ; auto.
  eelim (unique_def_spec_def x d1 d2) ; eauto.
Qed.
    
Lemma phi_src_dst_ninterlive : forall pc phib r1 r2 args,
  (fn_phicode tf) ! pc = Some phib ->
  In r2 args ->
  In (Iphi args r1) phib ->
  ninterlive_spec tf r2 r1.
Proof.
  intros. 
  exploit phi_resource_def ; go. intros [d Hd].
  econstructor; eauto.
  + intro. 
    eapply cssaliveout_use_def; eauto.
    eapply phiresources_use_def; go.
  + intro. 
    eapply cssaliveout_use_def; eauto.
    eapply phiresources_use_def; go.                  
  + intro ; subst.
    exploit phi_source_use_phicode; eauto. intros [d' [CFG USE]]. 
    exploit p_fn_jp_use_phib ; eauto; go. intros DEF.
    assert (d' = pc) by (eapply def_def_eq ; eauto; go); subst.
    invh use_phicode; eauto.
    assert ((fn_phicode tf) ! pc = None).
    { exploit index_pred_some_nth ; eauto. intros.
      unfold successors_list in H2. flatten H2.
      - eapply p_fn_normalized_jp with (pc:= pc0) ; go.
      - rewrite nth_error_nil_notSome_node in H2; go. 
    }
    go. 
Qed.

Lemma phi_unique_uses:
  forall pc phib args args' dst dst' r,
    (fn_phicode tf) ! pc = Some phib -> 
    In (Iphi args dst) phib ->
    In (Iphi args' dst') phib ->
    In r args ->
    In r args' ->
    dst = dst' /\ args = args'.
Proof.
  intros until r.
  intros PHIB  PHI1 PHI2 Hr1 Hr2. 
  eapply check_phicode_for_dups_in_phib_correct in PHIB; eauto.
  induction PHIB ; intros; go.
  invh NoDup.
  repeat invh In; auto.
  - split; go. 
  - eelim H with (x:= r) (y:= r) ; go.
  - eelim H with (x:= r) (y:= r) ; go.
  - unfold transl_function in * ; flatten TRANSL ; boolInv ; go.
Qed.  

Lemma phi_unique_uses_pc : forall pc phib args dst x r1 r2
  (PHICODE : (fn_phicode tf) ! pc = Some phib)
  (PHI : In (Iphi args dst) phib)
  (H : In r2 args)
  (H0 : In r1 args)
  (CFG : cfg tf x pc)
  (USE : use_phicode tf r1 x)
  (USE' : use_phicode tf r2 x)
  (DEF : assigned_parcopy_spec (fn_parcopycode tf) x r1)
  (DEF' : assigned_parcopy_spec (fn_parcopycode tf) x r2),
  r1 = r2.
Proof.
  intros.
  repeat invh use_phicode; eauto.      
  assert (SSAutils.is_edge f x pc) 
    by (invh cfg ; erewrite instructions_preserved in HCFG_ins ; go).
  exploit (p_parcb_inop f WF tf TRANSL x) ; go. 
  { invh assigned_parcopy_spec ; go. } intros [s Hnop]. 
  erewrite instructions_preserved in Hnop; eauto.
  exploit is_edge_pred ; eauto. intros [k1 Hk1].    
  assert (PREDpc :
            exists l, (make_predecessors (SSA.fn_code f) successors_instr) ! pc = Some l).
  { erewrite instructions_preserved in KPRED0; eauto.
    unfold index_pred, successors_list in * ; flatten KPRED; go.
  }
  destruct PREDpc as [ppc PREDpc].
  exploit index_pred_some_nth ; eauto. intros.
  eapply nth_error_some_in in H2.
  unfold successors_list in *.
  rewrite PREDpc in *.
  
  destruct (peq pc0 pc) ; destruct (peq pc1 pc); allinv; subst.
  * assert (phib1 = phib0) by congruence; subst.
    assert (phib0 = phib) by congruence; subst.
    assert (dst = dst1 /\ args = args1)
      by (eapply phi_unique_uses; eauto).
    invh and ; subst.
    assert (dst0 = dst1 /\ args0 = args1)
      by (eapply phi_unique_uses; eauto).
    invh and ; subst.
    congruence. 
  * exploit inop_is_not_in_two_preds; go. 
    eapply pred_is_edge_help in KPRED0; eauto.
    erewrite <- instructions_preserved in Hnop; eauto.
    invh is_edge ; allinv; simpl in * ; try invh or ; go. 
    erewrite <- instructions_preserved; eauto.
  * exploit inop_is_not_in_two_preds; go. 
    eapply pred_is_edge_help in KPRED; eauto.
    erewrite <- instructions_preserved in Hnop; eauto.
    invh is_edge ; allinv; simpl in * ; try invh or ; go. 
    erewrite <- instructions_preserved; eauto.
  * exploit inop_is_not_in_two_preds; go. 
    eapply pred_is_edge_help in KPRED0; eauto.
    erewrite <- instructions_preserved in Hnop; eauto.
    invh is_edge ; allinv; simpl in * ; try invh or ; go. 
    erewrite <- instructions_preserved; eauto.
    Unshelve.
    all: go.
Qed.

Theorem cssa_phi_live :
    forall pc resources, phi_resources tf pc resources -> 
                     forall r1 r2, 
                       In r1 resources -> 
                       In r2 resources -> 
                       r1 = r2 \/ ninterlive_spec tf r1 r2.
Proof.
  intros pc res Hphi r1 r2 Hr1 Hr2.
  invh phi_resources.
  destruct (peq r1 r2) ; subst ; auto.
  repeat invh In; allinv; auto.
  
  - (* Source and dest *) 
    right. eapply ninterlive_spec_sym; eauto.
    eapply phi_src_dst_ninterlive ; eauto. 
  - (* Dest and sources *)
    right.
    eapply phi_src_dst_ninterlive; eauto. 
  - (* Sources *) 
    right.
    assert (exists d1, def tf r1 d1) by (eapply phi_resource_def; go).
    assert (exists d2, def tf r2 d2) by (eapply phi_resource_def; go).
    repeat invh ex.
    econstructor; eauto.
    + intro. 
      eapply cssaliveout_use_def; eauto.
      eapply phiresources_use_def; go.
    + intro. 
      eapply cssaliveout_use_def; eauto.
      eapply phiresources_use_def; go.
    + intro ; subst.
      exploit phi_source_use_phicode; eauto. intros [d' [CFG USE]]. 
      exploit wf_cssa_extrainv_2; eauto; go. intros DEF.
      assert (d' = x) by (eapply def_def_eq ; eauto; go); subst.
      generalize H0. clear H0.
      exploit phi_source_use_phicode; eauto. intros [d'' [CFG' USE']]. 
      exploit wf_cssa_extrainv_2; eauto; go. intros DEF'. intros H0.
      assert (d'' = x) by (eapply def_def_eq ; eauto; go); subst.
      elim n; eapply phi_unique_uses_pc; eauto.
Qed.

End transl_function_Properties.

(* Final theorem to show in paper *)
Theorem cssa_phi_live_range : forall f tf,
       wf_ssa_function f ->
       transl_function f = Errors.OK tf ->
       forall (pc : node) (resources : list reg),
       phi_resources tf pc resources ->
       forall r1 r2 : reg,
       In r1 resources ->
       In r2 resources -> r1 = r2 \/ ninterlive_spec tf r1 r2.
Proof.
  intros; eauto using cssa_phi_live.
Qed.
