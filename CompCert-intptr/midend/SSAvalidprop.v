(** Some properties satisfied by well-typed functions with structural
    invariants. These are requirements for [wf_ssa_functions] *)

Require Import Classical.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Registers.
Require Import Floats.
Require Import Utils.

Require Import RTLdfs.
Require Import RTLutils.
 
Require Import Dom.
Require Import SSA. 
Require Import SSAutils. 
Require Import Conventions1.

Require Import SSAvalidspec.
Require Import Utilsvalidproof.
Require Import Kildall.
Require Import KildallComp.
Require Import Relation_Operators.
Require Import LightLive.
Require DomCompute.
Require Import Bijection.

Unset Allow StrictProp.

Notation path_step := (fun f => path_step (cfg f) (exit f) (fn_entrypoint f)).

Section WT_FUNCTION.

Variable size: nat.  
Variable f_rtl : RTLdfs.function.
Variable f : function.
Variable G : SSAvalid.tgamma.
Variable live: PMap.t Regset.t.

Hypothesis fn_wt : wt_function size f_rtl f live G.
Hypothesis fn_wfi : wf_init size f G.
Hypothesis fn_erased : check_erased_spec size f_rtl f.
Hypothesis fn_wfl : wf_live f_rtl (Lout live).

Hypothesis fn_ssa : unique_def_spec f.
Hypothesis fn_ssa_params1 : forall x pc, In x (fn_params f) -> ~ assigned_code_spec (fn_code f) pc x.
Hypothesis fn_ssa_params2 : forall x pc, In x (fn_params f) -> ~ assigned_phi_spec (fn_phicode f) pc x.

Hypothesis fn_reached : forall pc ins, (fn_code f) ! pc = Some ins -> reached f pc.
Hypothesis fn_entry : exists s, (fn_code f) ! (fn_entrypoint f) = Some (Inop s).
Hypothesis fn_phicode_code : forall pc block, 
    (fn_phicode f) ! pc = Some block -> 
    exists ins, (fn_code f) ! pc = Some ins.
Hypothesis fn_code_closed:
    forall pc pc' instr, f.(fn_code) ! pc = Some instr ->
    In pc' (successors_instr instr) -> 
    exists instr', f.(fn_code) ! pc' = Some instr'.
Hypothesis fn_entrypoint_inv: 
    (exists i, (f.(fn_code) ! (f.(fn_entrypoint)) = Some i)) /\ 
    ~ join_point f.(fn_entrypoint) f.
Hypothesis fn_code_inv2: forall jp pc i, (join_point jp f) ->
  In jp ((successors f) !!! pc) ->
  f.(fn_code) ! jp = Some i ->
  f.(fn_code) ! pc = Some (Inop jp).
Hypothesis fn_phicode_inv1: forall phib jp i,
    f.(fn_code) ! jp = Some i -> 
    f.(fn_phicode) ! jp = Some phib ->
    join_point jp f.
Hypothesis fn_phicode_inv2: forall jp i,
    join_point jp f ->
    f.(fn_code) ! jp = Some i -> 
    exists phib, f.(fn_phicode) ! jp = Some phib.

Notation ui := (erase_reg size).
Notation gi := (get_index size).
Notation entry := fn_entrypoint.

(** * Utility lemmas about indexed registers. *)
Lemma rmap_uigi : forall x,
    Bij.rmap size x = (ui x, gi x).
Proof.
  intros.
  unfold erase_reg, get_index.
  rewrite <- surjective_pairing.
  auto. 
Qed.
Hint Resolve rmap_uigi : bij.

(** * Utility lemmas on the erasure function *)
Lemma elim_structural : forall pc pc' instr instr' block,
  (fn_code f) ! pc = Some instr ->
  (fn_code f) ! pc' = Some instr' ->
  (fn_phicode f) ! pc' = Some block ->
  In pc' (successors_instr instr) -> instr = Inop pc'.
Proof.
  intros.
  exploit (fn_code_inv2 pc' pc) ; eauto.
  unfold successors_list.
  unfold successors.
  rewrite PTree.gmap1.
  unfold option_map. simpl. rewrite H. auto.
  intros. simpl in *; congruence.
Qed.

Lemma erased_funct_erased_instr_2: forall size pc f tf rinstr,
  check_erased_spec size f tf  ->
  (SSA.fn_code tf)!pc = Some rinstr ->
  exists pinstr,
    (RTLdfs.fn_code f) ! pc = Some pinstr
    /\ pinstr =  (erase_instr size rinstr).
Proof.
  clear.
  intros; inv H.
  exists (erase_instr size rinstr).
  split ; auto.
  rewrite HCODE ; eauto.
  unfold erase_code.  
  rewrite PTree.gmap. 
  unfold option_map. rewrite H0 ; auto.
Qed.

Lemma erased_assigned_code_spec : 
  forall pc x, 
    RTLutils.assigned_code_spec (RTLdfs.fn_code f_rtl) pc (ui x) ->
    exists rix idx,
      Bij.rmap size rix = ((ui x),idx) /\
      assigned_code_spec (fn_code f) pc rix.
Proof.
  intros.
  inv H;
  
  ((exploit_dstr erased_funct_erased_instr ; eauto);
  (unfold erase_instr in * ; destruct x0 ; allinv; try congruence; inv H4);

  try ((case_eq r; intros uix idx Hx);
  (exists idx ; unfold erase_reg in *; rewrite Hx in *;simpl in *);
  (destruct s0 ; congruence);
  (destruct s0 ; congruence);
  (destruct o ; congruence)));
  try (solve 
  [
    (destruct s0 ; congruence)
    | (destruct o ; congruence)]).
   
   - exists r.
     exists (snd (Bij.rmap size r)).
     split; try econstructor; eauto.
     rewrite H7.
     unfold erase_reg.
     rewrite <- surjective_pairing. auto. 

   - exists r.
     exists (snd (Bij.rmap size r)).
     split; try solve [econstructor; eauto].
     rewrite H8.
     unfold erase_reg.
     rewrite <- surjective_pairing. auto. 

   - exists r.
     exists (snd (Bij.rmap size r)).
     split; try solve [econstructor; eauto].
     destruct s0; inv H5.
     + rewrite H8.
       unfold erase_reg. rewrite <- surjective_pairing; auto. 
     + rewrite H8.
       unfold erase_reg. rewrite <- surjective_pairing; auto.

   - destruct b; inv H7; simpl in *; subst.
     rewrite H4 in *.
     exists x0.
     exists (snd (Bij.rmap size x0)).
     split; try solve [econstructor; eauto].
     unfold erase_reg. rewrite <- surjective_pairing; auto.     
Qed.

Lemma use_code_spec : 
  forall pc x, 
    use_code f x pc ->
    use_rtl_code f_rtl (ui x) pc.
Proof.
  intros.
  inv H ; 
  (exploit erased_funct_erased_instr_2 ; eauto);
  (intros [pinstr [Hcode Hins]]; inv Hins);
  (unfold erase_instr in * ; simpl in *).

   - econstructor 1 ; eauto; (eapply in_map ; eauto).
   - econstructor 2 ; eauto; (eapply in_map ; eauto).
   - econstructor 3 ; eauto; (eapply in_map ; eauto).
   - econstructor 4 ; eauto.
     generalize H1. clear.
     revert x.
     induction args; intros; auto.
     simpl in *.
     apply in_app_or in H1. inv H1.
     + apply in_or_app. left.
       revert H. clear.
       induction a ; simpl; intros ; auto.
       * intuition; subst; auto.
       * apply in_app_or in H. inv H; apply in_or_app; auto.
       * apply in_app_or in H. inv H; apply in_or_app; auto.
     + apply in_or_app; eauto.
   - econstructor 5 ; eauto. inv H1; eauto. econstructor 2 ; eauto. (eapply in_map ; eauto).
   - econstructor 6 ; eauto. inv H1; eauto. econstructor 2 ; eauto. (eapply in_map ; eauto).
   - econstructor 8 ; eauto. inv H1; eauto. econstructor 2 ; eauto. (eapply in_map ; eauto).
   - econstructor 7 ; eauto. (eapply in_map ; eauto).
   - econstructor 9 ; eauto. (eapply in_map ; eauto).
   - econstructor 10 ; eauto. 
   - econstructor 11 ; eauto. 
Qed.

Lemma use_ins_code : forall pc x, 
  use f x pc ->
  exists ins, (fn_code f) ! pc = Some ins.
Proof.
  intros. inv H.
  inv H0 ; eauto.
  inv H0. 
  exploit index_pred_some_nth; eauto. intros. 
  exploit nth_error_some_in ; eauto. intros.
  eapply (make_predecessors_some (fn_code f) successors_instr pc0) ; eauto.
  unfold make_preds, successors_list in *. 
  destruct ((make_predecessors (fn_code f) successors_instr) ! pc0). auto.
  inv H0. 
Qed.

(** * Utility lemmas about [cfg] [edge], and [path] *)    
Hint Constructors rtl_cfg: core.

Lemma cfg_rtl_cfg : forall size f tf pc1 pc2,
  check_erased_spec size f tf ->
  cfg tf pc1 pc2 -> 
  rtl_cfg f pc1 pc2.
Proof.
  clear. intros.
  inv H0.
  exploit erased_funct_erased_instr_2 ; eauto.
  intros [pinstr [Hcode Hins]]. inv Hins.
  destruct ins; simpl in * ; eauto.
  (destruct s0; allinv; (inv HCFG_in; eauto)).
  econstructor; eauto; simpl; auto.
  intuition.
  econstructor; eauto; simpl; auto.
  intuition.
  econstructor; eauto; simpl; auto.
  intuition.
  econstructor; eauto; simpl; auto.
  intuition.
Qed.  

Import DLib.
    
Notation path := (fun f => path (cfg f) (exit f) (entry f)).

Lemma path_first : forall p pc pc', 
  path f (PState pc) p (PState pc') ->
  pc <> pc' ->
  exists pc'', exists p', exists p'',
    path f (PState pc) p' (PState pc'') /\
    ~ In pc' p' /\
    pc'' <> pc' /\
    path_step f (PState pc'') pc'' (PState pc') /\
    p = p'++(pc''::p'').
Proof.
  clear.
    induction p ; intros; inv H. 
    congruence.
    assert (a = pc) by (inv STEP; auto). inv H.
    destruct s2.
    destruct (peq pc0 pc').
    (* peq *)
    inv e.  exists pc. exists nil. exists p.
    split; eauto.  econstructor ; eauto.
    (* diff *)
    exploit IHp ; eauto. intros [pc'' [p'  [p'' [Hp' [Hpc'' [Hdiff [Hnotin Happ]]]]]]].
    exists pc''. exists (pc::p'). exists p''.
    split ; auto.
    econstructor ; eauto. 
    split ; auto.
    intro Hcont. inv Hcont. congruence. elim Hpc'' ; auto.
    split. intro Hcont. inv Hcont. congruence.
    split ; eauto. simpl. rewrite Happ ; auto.
    exploit (@path_from_ret_nil node); eauto. intros Heq ; subst. 
    inv PATH.
  Qed.

Lemma use_reached : forall pc x, 
  use f x pc ->
  reached f pc.
Proof.
  intros.
  exploit use_ins_code ; eauto.
  intros [ins Hins]. 
  eapply fn_reached ; eauto.  
Qed.

(** * Tactics *)
Ltac error_struct tf pc pc' :=
  (match goal with
     | [ H1 : (fn_code tf) ! pc = Some _ ,
         H2 : (fn_phicode tf) ! pc' = Some _
       |- _ ] =>
       let Hcont := fresh "Hcont" in
       let HHcont := fresh "Hcont" in 
       (exploit (fn_code_closed pc pc') ; eauto) ;
       (allinv ; simpl ; auto) ;
       (intros [ins' Hins'] ; (exploit (elim_structural pc pc'); eauto);
         [ allinv ; (simpl) ; auto | (intros HHcont; inv HHcont)])
     | [ H1 : (fn_code tf) ! pc = Some _ ,
         H2 : (fn_phicode tf) ! pc' = Some _
         |- _ ] =>
       let HHcont := fresh "Hcont" in 
       (exploit (fn_code_closed pc pc') ; eauto);
       (intros [ins' Hins'] ; (exploit (elim_structural pc pc'); eauto)) ;
       (intro HHcont ; inv HHcont)
   end).

Ltac well_typed :=
  match goal with
    | [ Hwt : wt_instr _ _ _ _ |- _ ] => inv Hwt
  end.

Lemma use_code_valid_reg : forall x pc,
    use_code f x pc ->
    Bij.valid_reg_ssa size x = true.
Proof.
  inv fn_wt.
  induction 1 ; intros;
    try (assert (He: is_edge f pc s) by go;
         (exploit WTE; eauto); (intros Hwte; inv Hwte; allinv);
         [ well_typed; eauto
         | error_struct f pc s]
        ).
  - assert (He: is_out_node f pc) by go.
    exploit WTO; eauto. intros Hwte. inv Hwte; allinv.
    well_typed; eauto.
  - assert (He: is_out_node f pc) by go.
    exploit WTO; eauto. intros Hwte. inv Hwte; allinv.
    well_typed; eauto.
  - destruct tbl.
    + assert (He: is_out_node f pc) by go.
      exploit WTO; eauto. intros Hwte. inv Hwte; allinv.
      well_typed; eauto.
    + assert (He: is_edge f pc n) by go.
      exploit WTE; eauto. intros Hwte. inv Hwte; allinv.
      * well_typed; eauto.
      * error_struct f pc n.
  - assert (He: is_out_node f pc) by go.
    exploit WTO; eauto. intros Hwte. inv Hwte; allinv.
    well_typed; eauto.
Qed.

Lemma use_phicode_valid_reg: forall x pc,
    use_phicode f x pc ->
    Bij.valid_reg_ssa size x = true.
Proof.
  inv fn_wt. intros ? ? PHIU. inv PHIU.
  exploit pred_is_edge ; eauto. intros Hedge.
  (exploit WTE ; eauto ; intros Hwte). 
  inv Hwte; allinv. 
  inv WTPHID0.
  destruct (Bij.rmap size dst) as (dstr, dsti) eqn:EQ.
  exploit USES; eauto. intros PHIU.
  exploit index_pred_some_nth ; eauto. intros Hnth.
  exploit (@list_map_nth_some node (Registers.reg -> positive) G) ; eauto. intros Hnth'.
  exploit phiu_nth ; eauto. intuition. 
Qed.

Lemma def_code_valid_reg : forall x pc,
    assigned_code_spec (fn_code f) pc x ->
    Bij.valid_reg_ssa size x = true.
Proof.
  inv fn_wt.
  induction 1 ; intros.

  - assert (He: is_edge f pc succ) by go.
    (exploit WTE; eauto); (intros Hwte; inv Hwte; allinv).
    + well_typed; eauto.
    + error_struct f pc succ.
  - assert (He: is_edge f pc succ) by go.
    (exploit WTE; eauto); (intros Hwte; inv Hwte; allinv).
    + well_typed; eauto.
    + error_struct f pc succ.
  - assert (He: is_edge f pc succ) by go.
    (exploit WTE; eauto); (intros Hwte; inv Hwte; allinv).
    + well_typed; eauto.
    + error_struct f pc succ.
  - assert (He: is_edge f pc succ) by go.
    (exploit WTE; eauto); (intros Hwte; inv Hwte; allinv).
    + well_typed; eauto. eelim H6; eauto.
    + error_struct f pc succ.
Qed.

Lemma def_phicode_valid_reg: forall x pc,
    assigned_phi_spec (fn_phicode f) pc x ->
    Bij.valid_reg_ssa size x = true.
Proof.
  inv fn_wt. intros ? ? PHID. inv PHID.
  destruct H0 as [args Hin].
  exploit fn_phicode_code ; eauto. intros [ins Hins].
  exploit fn_phicode_inv1 ; eauto. intros Hjp.
  inv Hjp. 
  assert (Hpred : exists d k,
             index_pred (make_predecessors (fn_code f) successors_instr) d pc = Some k).
  { assert (exists d, In d l).
    destruct l; simpl in *.
    apply False_ind; lia.
    eauto.
    destruct H0 as [pc' H1].
    exists pc'.
    assert (In pc' ((make_predecessors (fn_code f) successors_instr)!!!pc)).
    { unfold successors_list; rewrite Hpreds; auto. }
    exploit @make_predecessors_some ; eauto. intros (ipc & Hpc).
    exploit @make_predecessors_correct2; eauto. intros Hind.
    eapply index_pred_instr_some ; eauto.
  }
  destruct Hpred as [pred [k Hidxp]].  
    exploit pred_is_edge ; eauto. intros Hedge.
    (exploit WTE ; eauto ; intros Hwte). 
    inv Hwte; allinv. 
    inv WTPHID.
    eapply VALIDR; eauto. go. 
Qed.

Lemma def_valid_reg : forall x pc,
    def f x pc ->
    Bij.valid_reg_ssa size x = true.
Proof.
  intros ? ? DEF.
  inv DEF.
  - inv H.
    + inv fn_wfi.
      exploit H; eauto. intuition.
    + destruct H0 as [pc Huse]; inv Huse.
      * eapply use_code_valid_reg; eauto.
      * eapply use_phicode_valid_reg; eauto.
  - eapply def_code_valid_reg; eauto. 
  - eapply def_phicode_valid_reg; eauto.
Qed.

(** * Properties required for [wf_ssa_function]  *)

Lemma unique_def_spec_def : forall x d1 d2, 
  def f x d1 -> def f x d2 -> d1 <> d2 ->  False.
Proof.
  intros.
  destruct fn_ssa as [Hssa1 Hssa2].
  destruct fn_entry as [succ Hentry].
  inv H ; inv H0 ; inv H ; inv H2; 
  try congruence;
  try solve [
      exploit fn_ssa_params1 ; eauto
    | exploit fn_ssa_params2 ; eauto
    | exploit H3 ; eauto 
    | exploit H4 ; eauto; intuition
    |   (eelim (Hssa1 x d1 d2) ; eauto; intuition subst; eauto)].
Qed.

Lemma use_code_gamma : forall u x
  (USE : use_code f x u),
  G u (ui x) = (gi x).
Proof.
  intros.
  destruct (Bij.rmap size x) as (rx,ridx) eqn:EQ; simpl in *.
  inv USE;
  match goal with 
    | [Hins : (fn_code f) ! u = Some (Icall _ _ _ _ _) |- _ ] => inv H0
    | [Hins : (fn_code f) ! u = Some (Itailcall _ _ _) |- _ ] => inv H0
    | [Hins : (fn_code f) ! u = Some (Ijumptable _ _) |- _ ] => 
      destruct tbl as [ | s succ]; [ idtac  |]
    | _ => idtac
  end ;
  let tac := ((inv fn_wt);
      ((assert (Ho : is_out_node f u) by ( solve [econstructor 2 ; eauto | econstructor 1 ; eauto])) ;
        (exploit (WTO u) ; eauto ; intro Hwto) ;
        (inv Hwto; allinv; try error_struct f u s);
        ( well_typed ; eauto using rmap_uigi))) in 
  (match goal with 
    | [Hins : (fn_code f) ! u = Some (Ireturn _) |- _ ] => tac
    | [Hins : (fn_code f) ! u = Some (Itailcall _ _ _) |- _]  => tac            
    | _ => 
      try ((inv fn_wt);
      ((assert (He : is_edge f u s) by (econstructor ; eauto ; simpl ; auto)) ;
          (exploit (WTE u s) ; eauto ; intro Hwte);
          (inv Hwte; allinv; try error_struct f u s);
          ( well_typed ; eauto using rmap_uigi)))
  end).  

  ((inv fn_wt);
   ((assert (Ho : is_out_node f u) by ( solve [econstructor 3 ; eauto | econstructor 1 ; eauto])) ;
    (exploit (WTO u) ; eauto ; intro Hwto) ;
    (inv Hwto; allinv; try error_struct f u s);
    ( well_typed ; eauto using rmap_uigi))). 
Qed.
    
Lemma use_phicode_gamma : forall u x
  (USE : use_phicode f x u),
  G u (ui x) = (gi x).
Proof.
  intros.
  inv USE. 
  inv fn_wt. 
  assert (He : is_edge f u pc) by (eapply pred_is_edge ; eauto).

  exploit WTE ; eauto ; intro Hwte.
  inv Hwte ; allinv.
  inv WTPHID0.
  destruct (Bij.rmap size x) as (rx, ix) eqn:Hx.
  unfold erase_reg, get_index ; inv Hx ; simpl.
  destruct (Bij.rmap size dst) as (rdst, idst) eqn:Hdst.
  exploit USES ; eauto. intro Hphiu. 
  exploit index_pred_some_nth ; eauto. intros Hnth.
  exploit (@list_map_nth_some node (Registers.reg -> positive) G) ; eauto. intros Hnth'.
  exploit phiu_nth ; eauto. intros [HVALIDR [i [Hbij' [HG HVALIDI]]]].
  
  assert (EQ: (rx, ix) = (rdst,i)) by congruence; inv EQ.
  rewrite Hbij'; auto.
Qed.
  
Lemma use_gamma : forall x u, 
  use f x u ->
  G u (ui x) = gi x.
Proof.
  intros. inv H. 
  eapply use_code_gamma ; eauto.
  eapply use_phicode_gamma ; eauto.
Qed.

Lemma wt_use_isdef : forall x u,  use f x u -> exists d, def f x d.
Proof.
  intros.
  exploit use_gamma ; eauto. intros HGamma.
  destruct (classic (exists pc, assigned_code_spec (fn_code f) pc x)).
  destruct H0. eauto.
  destruct (classic (exists pc, assigned_phi_spec (fn_phicode f) pc x)).
  destruct H1. eauto.
  inv fn_wfi.
  exists (fn_entrypoint f). eauto.
  econstructor ; eauto.
  econstructor 2 ; eauto.
Qed.

Lemma gamma_entry_param : forall x d, 
  G (entry f) (ui x) = gi x ->
  def f x d ->
  d = (entry f).
Proof.
  intros. inv fn_wt.
  inv H0.
  - (* entry *)
    auto.
  - (* defined in code *)
    inv H1;
      (assert (Hedge : is_edge f d succ) by (econstructor; eauto; simpl; auto)) ;
      (exploit WTE ; eauto ; intros Hwte;
       (inv Hwte; allinv; [
          inv EIDX ;
          unfold ui, gi in *;
          try match goal with
          | id: Bij.rmap size ?x = _ |- _ => rewrite id in *
          end;
          simpl in *; congruence; fail
        | error_struct f d succ])).
  - (* defined in phicode *)
    inv H1. destruct H2 as [args Hin].
    exploit fn_phicode_code ; eauto. intros [ins Hins].
    exploit fn_phicode_inv1 ; eauto. intros Hjp.
    inv Hjp. 
    assert (Hpred : exists pc k,
               index_pred (make_predecessors (fn_code f) successors_instr) pc d = Some k).
    { assert (exists pc, In pc l).
      destruct l; simpl in *.
      apply False_ind; lia.
      eauto.
      destruct H1 as [pc H1].
      exists pc.
      assert (In pc ((make_predecessors (fn_code f) successors_instr)!!!d)).
      { unfold successors_list; rewrite Hpreds; auto. }
      
      exploit @make_predecessors_some ; eauto. intros (ipc & Hpc).
      exploit @make_predecessors_correct2; eauto. intros Hind.
      eapply index_pred_instr_some ; eauto.
    }
    destruct Hpred as [pred [k Hidxp]].  
    exploit pred_is_edge ; eauto. intros Hedge.
    (exploit WTE ; eauto ; intros Hwte). 
    inv Hwte; allinv. 
    inv PEIDX. exploit (H1 x) ; eauto. econstructor ; eauto.
    eapply rmap_uigi. intuition.
Qed.
    
Lemma gamma_path_def : forall p s,
  DomCompute.path f p s ->
  match s with 
    | PStop => True
    | PState pc =>
      forall xi x d i,
        Bij.rmap size xi = (x,i) ->
        def f xi d ->
        G pc x = i ->
        Regset.In x (Lin f_rtl pc (Lout live)) -> 
        (In d p
          \/ (d = pc /\ 
            ~ ( use_code f xi pc /\ 
              assigned_code_spec (fn_code f) pc xi)))
  end.
Proof.
  induction 1 ; intros ; auto. 

  - (* nil : defined in params *)
    right.
    exploit gamma_entry_param ; eauto. 
    + unfold erase_reg,  get_index. rewrite H. simpl; auto.
    + intro Heq; subst ; split ; auto. 
      intros [_ Hcont2].  destruct fn_entry  as [se Hentry].
      inv Hcont2 ; allinv.
  
  - (* pc::p *)
    assert (is_edge f pc pc') by (econstructor ; eauto).
    generalize fn_wt; intros WELL_TYPED. inv WELL_TYPED.
    
    destruct (classic (Regset.In x (Lin f_rtl pc (Lout live)))).
    
    + exploit WTE ; eauto. intros Hwte.
      inv Hwte; allinv. destruct ins.
      
      * (* nop *)
        inv WTI. rewrite <- H8 in *. exploit IHpath ; eauto.
        intros [HH1 | [HH21 HH22]]. 
        left ; eauto.
        inv HH21. left ; eauto.
    
      * (* iop *)  
        inv WTI. 
        destruct (p2eq (x, G pc' x) (r0,i)).
        -- (* x is def at pc *)
          inv e. 
          left. left.
          destruct (peq d pc); auto.
          exploit (unique_def_spec_def xi d pc) ; eauto.
          assert (r = xi).
          { eapply Bij.INJ; eauto; [| congruence].
            eapply def_valid_reg; eauto.
          }
          subst. repeat econstructor; eauto.          
          intuition.  
   
        -- (* another x version is def at pc *)
          exploit (IHpath xi)  ; eauto.
          ++ rewrite <- H10.
             unfold update. destruct (peq x r0).
             ** inv e. elim n0. rewrite <- H10.
                unfold update ; unfold erase_reg. 
                rewrite peq_true; auto.
             ** auto.

          ++ intros [HH1 | [HH21 HH22]]. 
             left ; eauto.
             inv HH21 ; eauto.
             
      * (* iload *)  
        inv WTI. 
        
        destruct (p2eq (x, G pc' x) (r0, i)).
        (* x is def at pc *)
        inv e. 
        left ; left.
        destruct (peq d pc); auto.
        assert (r = xi).
        { eapply Bij.INJ; eauto; [| congruence].
          eapply def_valid_reg; eauto.
        }
        subst.
        exploit (unique_def_spec_def xi d pc) ; eauto.
        intuition.  
        
        (* another x version is def at pc *)
        exploit (IHpath xi) ; eauto.
        rewrite <- H12.
        unfold update. destruct (peq x r0).
        inv e. elim n0. rewrite <- H12.
        unfold update, erase_reg. 
        rewrite peq_true. 
        auto.
        auto.

        intros [HH1 | [HH21 HH22]]. 
        left ; eauto.
        inv HH21 ; eauto.

      * (* istore *)  
        inv WTI ; rewrite <- H12 in * ; eauto.
        exploit IHpath ; eauto. 
        intros [HH1 | [HH21 HH22]]. 
        left ; eauto.
        inv HH21 ; eauto.
 
      * (* icall *)  
        inv WTI. 
        
        destruct (p2eq (x, G pc' x) (r0, i)).
        (* x is def at pc *)
        inv e. unfold erase_reg, get_index in * ; simpl in *. 
        left ; left.
        destruct (peq d pc); auto.
        assert (r = xi).
        { eapply Bij.INJ; eauto; [| congruence].
          eapply def_valid_reg; eauto.
        }
        subst.
        exploit (unique_def_spec_def xi d pc) ; eauto.
        intuition.  
        
        (* another x version is def at pc *)
        exploit (IHpath xi) ; eauto.
        rewrite <- H12.
        unfold update. destruct (peq x r0).
        inv e. elim n0. rewrite <- H12.
        unfold update, erase_reg. 
        rewrite peq_true. 
        auto.
        auto.

        intros [HH1 | [HH21 HH22]]. 
        left ; eauto.
        inv HH21 ; eauto.

        destruct (p2eq (x, G pc' x) (r0, i)).
        (* x is def at pc *)
        inv e. unfold erase_reg, get_index in * ; simpl in *. 
        left ; left.
        
        destruct (peq d pc); auto.
        assert (r = xi).
        { eapply Bij.INJ; eauto; [| congruence].
          eapply def_valid_reg; eauto.
        }
        subst.
        exploit (unique_def_spec_def xi d pc) ; eauto.
        intuition.  
   
        (* another x version is def at pc *)
        exploit (IHpath xi) ; eauto.
        rewrite <- H12.
        unfold update. destruct (peq x r0).
        inv e. elim n0. rewrite <- H12.
        unfold update, erase_reg. 
        rewrite peq_true. 
        auto.
        auto.

        intros [HH1 | [HH21 HH22]]. 
        left ; eauto.
        inv HH21 ; eauto.  
  
      * (* itailcall *)  
        inv WTI. rewrite <- H9 in * ; eauto.
        exploit IHpath ; eauto.
        intros [HH1 | [HH21 HH22]]. 
        left ; eauto.
        inv HH21 ; eauto.

        rewrite <- H9 in * ; eauto.
        exploit IHpath ; eauto.
        intros [HH1 | [HH21 HH22]]. 
        left ; eauto.
        inv HH21 ; eauto.

      * (* builtin *)
        { inv WTI.     
          
          - (* Builtin res assigned *)
            destruct (p2eq (x, G pc' x) (r, i)).
            + (* x is def at pc *)
              inv e0. 
              left ; left. 
              destruct (peq d pc); auto.
              assert (x0 = xi).
              { eapply Bij.INJ; eauto; [| congruence].
                eapply def_valid_reg; eauto.
              }
              subst.
              exploit (unique_def_spec_def xi d pc) ; eauto.
              intuition.  
            + (* another x version is def at pc *)
              exploit (IHpath xi) ; eauto.
              rewrite <- H10.
              unfold update. destruct (peq x r).
              subst.
              elim n0.
              rewrite <- H10.
              unfold update; rewrite peq_true ;auto.
              auto.

              intros [HH1 | [HH21 HH22]]. 
              left ; eauto.
              inv HH21 ; eauto.
              
          - (* Builtin with no res assigned *)
            exploit IHpath; eauto.
            rewrite H10; auto.
            intros [HH1 | [HH21 HH22]]. 
            left ; eauto.
            inv HH21 ; eauto.
        }
  
      * (* icond *)  
        inv WTI. rewrite <- H11 in * ; eauto.
        exploit IHpath ; eauto.
        intros [HH1 | [HH21 HH22]]. 
        left ; eauto.
        inv HH21 ; eauto.

      * (* ijmptable *)  
        inv WTI. rewrite <- H7 in * ; eauto.
        exploit IHpath ; eauto.
        intros [HH1 | [HH21 HH22]]. 
        left ; eauto.
        inv HH21 ; eauto.
  
      * (* ireturn *)
        inv WTI. rewrite <- H6 in * ; eauto.
        exploit IHpath ; eauto.
        intros [HH1 | [HH21 HH22]]. 
        left ; eauto.
        inv HH21 ; eauto.

        rewrite <- H8 in * ; eauto.
        exploit IHpath ; eauto.
        intros [HH1 | [HH21 HH22]]. 
        left ; eauto.
        inv HH21 ; eauto.
  
      * (* join point at pc' *)
        inv WTPHID.
        destruct (classic (assigned xi block)).
   
        -- (*  assig in the block *)
          right.
          assert (d = pc').
          destruct (peq d pc'); auto.
          exploit (unique_def_spec_def xi d pc') ; eauto.
          intuition.  split ; auto. 
          
          intros [Hcont1 Hcont2].
          inv H5. 
          inv fn_ssa. 
          destruct (H5 xi pc' pc') as [_ [_ [Hcont _]]].
          exploit Hcont ; eauto.  
  
        -- (* not assig in the block *) 
          destruct (classic (erased_reg_assigned size x block)).
          ++ inv H6. inv H7.
             destruct (Bij.rmap size x0) as (r, p0) eqn:Hx0; simpl in *. 
             exploit (ASSIG x0); eauto. 
             right.
             unfold ui in *.
             rewrite Hx0 in *. simpl in *. rewrite H7 in *.
             assert (x0 = xi).
             { eapply Bij.INJ; eauto. 
               eapply def_valid_reg; eauto.
               congruence.
             }
             subst.
             assert (d = pc').
             { destruct (peq d pc') ; auto. 
               intuition. 
             }
             intuition.

          ++ exploit (NASSIG x) ; eauto.
             intros. intros Hcont.  elim H6. 
             exists ri. split ; auto.
             unfold ui. rewrite H7 ; auto.
             intros [HH1 | HH2].
             
             rewrite HH1 in * ; eauto.
             exploit IHpath ; eauto.
             intros [HH1' | [HH21' HH22']]. 
             left ; eauto.
             inv HH21' ; eauto.
  
             intuition.
  
    + (* x not live at pc *)
      exploit (wf_live_incl f_rtl (Lout live) fn_wfl pc pc')  ; eauto.
      eapply cfg_rtl_cfg ; eauto. econstructor ; eauto.
      intros [HH1 | HH2]; auto. 
      intuition. 

      exploit (erased_assigned_code_spec pc xi) ; eauto.
      unfold ui; rewrite H0; auto.
      intros [rix [idx [Hrmap Hass]]]. 
      inv Hass ; allinv.
      
      * (* iop *)
        exploit WTE ; eauto.
        intros Hwte. inv Hwte ; allinv ; try (error_struct f pc pc').
        
        inv WTI.
        rewrite <- H10 in *. 
        assert (HEQ: (r, i) = (ui xi, idx)) by congruence. inv HEQ.
        unfold ui in *. rewrite H0 in *. simpl fst in *.
        assert (HEQ: fst (Bij.rmap size xi) = x).
        { rewrite H0; auto. }
        rewrite HEQ in *.
        unfold update in * ; rewrite peq_true in *.
        
        assert (d = pc).
        destruct (peq d pc); auto.
        assert (rix = xi).
        { eapply Bij.INJ; eauto; [| congruence].
          eapply def_valid_reg; eauto.
        }
        subst. 
        exploit (unique_def_spec_def xi d pc) ; eauto.
        intuition.  inv H5. eauto. 

      * (* load *)
        exploit WTE ; eauto.
        intros Hwte. inv Hwte ; allinv ; try (error_struct f pc pc').
        
        inv WTI.
        rewrite <- H12 in *. 
        assert (HEQ: (r, i) = (ui xi, idx)) by congruence. inv HEQ.
        unfold ui in *. rewrite H0 in *. simpl fst in *.
        assert (HEQ: fst (Bij.rmap size xi) = x).
        { rewrite H0; auto. }
        rewrite HEQ in *.
        unfold update in * ; rewrite peq_true in *.

        assert (d = pc).
        destruct (peq d pc); auto.
        assert (rix = xi).
        { eapply Bij.INJ; eauto; [| congruence].
          eapply def_valid_reg; eauto.
        }
        subst. 
        exploit (unique_def_spec_def xi d pc) ; eauto.
        intuition. inv H5. auto. 

                      
      * (* icall *)
        exploit WTE ; eauto.
        intros Hwte. inv Hwte ; allinv ; try (error_struct f pc pc').
        
        inv WTI.
        rewrite <- H12 in *.
        assert (HEQ: (r, i) = (ui xi, idx)) by congruence. inv HEQ.
        unfold ui in *. rewrite H0 in *. simpl fst in *.
        assert (HEQ: fst (Bij.rmap size xi) = x).
        { rewrite H0; auto. }
        rewrite HEQ in *.
        unfold update in * ; rewrite peq_true in *.
        
        assert (d = pc).
        destruct (peq d pc); auto.
        assert (rix = xi).
        { eapply Bij.INJ; eauto; [| congruence].
          eapply def_valid_reg; eauto.
        }
        subst. 
        exploit (unique_def_spec_def xi d pc) ; eauto.
        intuition.  inv H5. auto. 

        rewrite <-H12 in *.
        
        assert (HEQ: (r, i) = (ui xi, idx)) by congruence. inv HEQ.
        unfold ui in *. rewrite H0 in *. simpl fst in *.
        assert (HEQ: fst (Bij.rmap size xi) = x).
        { rewrite H0; auto. }
        rewrite HEQ in *.
        unfold update in * ; rewrite peq_true in *.
        
        assert (d = pc).
        destruct (peq d pc); auto.
        assert (rix = xi).
        { eapply Bij.INJ; eauto; [| congruence].
          eapply def_valid_reg; eauto.
        }
        subst. 
        exploit (unique_def_spec_def xi d pc) ; eauto.
        intuition.  inv H5. auto. 
  
      * (* builtin *)
        exploit WTE ; eauto.
        intros Hwte. inv Hwte ; allinv ; try (error_struct f pc pc').
        
        inv WTI.
        -- rewrite <- H10 in *. 
           assert (HEQ: (r, i) = (ui xi, idx)) by congruence. inv HEQ.
           unfold ui in *. rewrite H0 in *. simpl fst in *.
           assert (HEQ: fst (Bij.rmap size xi) = x).
           { rewrite H0; auto. }
           rewrite HEQ in *.
           unfold update in * ; rewrite peq_true in *.
           
           assert (d = pc).
           destruct (peq d pc); auto.
           assert (rix = xi).
           { eapply Bij.INJ; eauto; [| congruence].
             eapply def_valid_reg; eauto.
           }
           subst. 
           exploit (unique_def_spec_def xi d pc) ; eauto.
           intuition. inv H5. auto.
        -- eelim H11; eauto. 
Qed.

Lemma gamma_def_path : forall p pc xi x i d,
  Bij.rmap size xi = (x,i) ->
  def f xi d ->
  G pc x = i ->
  DomCompute.path f p (PState pc) -> 
  Regset.In x (Lin f_rtl pc (Lout live)) -> In d (pc::p).
Proof.
  intros.
  exploit gamma_path_def ; eauto.
  simpl. intros. exploit H4 ; eauto.
  intros [HH1 | [HH21 HH22]].
  right ; auto. 
  inv HH21. left ; auto.
Qed.

Lemma phiu_same_length : forall r args gammas, 
  phiu size r args gammas ->
  length args = length gammas.
Proof.
  induction 1 ; intros ; eauto.
  simpl. eauto.
Qed.

Lemma wt_phiu_args_dst : forall pc phib args dst k xi x i,
  (fn_phicode f) ! pc = Some phib ->
  In (Iphi args dst) phib ->
  nth_error args k = Some xi ->
  Bij.rmap size xi = (x, i) ->
  wt_phiu size (make_predecessors (fn_code f) successors_instr) !!! pc phib G ->
  exists idx, Bij.rmap size dst = (x, idx).
Proof.
  intros.
  inv H3.
  destruct (Bij.rmap size dst) as (rdst, idst) eqn: EQ. 
  exploit USES ; eauto. intros Hphiu. 
  set (gammas := (map G (make_predecessors (fn_code f) successors_instr) !!! pc)) in *.
  exploit phiu_same_length ; eauto. intros Hlength.
  exploit @nth_error_some_same_length ; eauto. intros [e Hnthgammas].
  exploit phiu_nth ; eauto. intros [HVALIDR [i0 [Hxi' [Hi0 HVALIDI]]]].
  assert (HEQ: (x, i) = (rdst, i0)) by congruence; inv HEQ.
  eauto.
Qed. 

Lemma wt_pdom : forall x u d
  (USE: use f x u)
  (DEF: def f x d),
  dom f d u.
Proof. 
  intros.
  destruct (peq u d).  inv e ; econstructor ; eauto.

  eelim (classic (dom f d u)) ; eauto. intro Hcont.
  assert (exists p, path f (PState (entry f)) p (PState u) /\ ~ In d p).

  eapply (@not_dom_path_wo node peq) ; eauto.  eapply use_reached ; eauto. 
  destruct H as [p [Hp Hnotin]].
  
  exploit use_gamma ; eauto. intro HGamma.
    
  destruct (Bij.rmap size x) as [rx i] eqn: EQ.
  unfold ui, gi in *. rewrite EQ in *; simpl in *.

  exploit DomCompute.SSA_path_this_path ; eauto. intros Hpath.
  exploit gamma_def_path ; eauto.
  
  - invh use. 
    + (* use in code *)
      eapply wf_live_use ; eauto. 
      eapply use_code_spec in H ; eauto.
      unfold ui, gi in *. rewrite EQ in *; simpl in *.
      auto.
    + (* use in phicode *)
      inv H. 
      assert (Hedge : is_edge f u pc) by (eapply pred_is_edge ; eauto).
      inv fn_wt. exploit WTE ; eauto. intros Hwte. inv Hwte ; allinv.
      exploit (wt_phiu_args_dst pc block args dst k x rx (G u rx)); eauto. intros [idx Hidx].  
  
      assert (Hlpc : Regset.In rx (Lin f_rtl pc (Lout live))).
      { inv WTPHID. exploit (LIVE dst rx idx) ; eauto. econstructor ; eauto. }
      intros.
      exploit (wf_live_incl f_rtl (Lout live) fn_wfl u pc) ; eauto.
      { eapply cfg_rtl_cfg ; eauto. inv Hedge ; eauto.
        econstructor ; eauto.
      }
      intros [HH1 | HH2]; auto.
      exploit fn_phicode_code ; eauto. intros [ins0 Hins0].
      exploit fn_phicode_inv1 ; eauto. intros Hjp. 
      exploit (fn_code_inv2 pc u) ; eauto. 
      { inv Hedge. unfold successors_list, successors. rewrite PTree.gmap1.
        unfold option_map. rewrite H ; auto.
      } intros Hcode.
      inv fn_erased. 
      inv HH2; rewrite HCODE in H;
        (
          (unfold erase_code in H; rewrite PTree.gmap in H);
          (unfold option_map in H; rewrite Hcode in H);
          (inv H)).

  - intros Hcont'.  inv Hcont'.
    econstructor ; eauto. 
    elim Hnotin. eapply in_rev ; eauto. 
Qed.  

Lemma wt_def_use_code_false : forall x pc
  (USE: use_code f x pc)
  (DEF: assigned_code_spec (fn_code f) pc x),
  False.
Proof.
  intros.
  destruct (Bij.rmap size x) as (r, idx) eqn: Hrmap.
  
  exploit use_code_gamma ; eauto; intros Hgamma.
  exploit use_code_spec ; eauto. intros Hrtl.  
  exploit wf_live_use ; eauto. intros Hlive.
  assert (Htmp : use f x pc). econstructor ; eauto. exploit wt_use_isdef ; eauto. intros [d Hdef].
  unfold get_index, erase_reg in *. rewrite Hrmap in * ; simpl in *.
  
  exploit use_reached ; eauto. intros Rpc.
  exploit (@reached_path node) ; eauto. intros [p Hp].  
  exploit (path_first p (entry f)) ; eauto. 
  intro Hcont. inv Hcont. inv fn_wt. destruct fn_entry. inv USE; allinv.
  intros [pc' [p' [p'' [Hp' [Hnotin [Hdiff [Hpc' Happ]]]]]]]. 
  
  assert (DomCompute.path f (pc'::(rev p')) (PState pc)).  
  { inv Hpc'.
    inv STEP. 
    econstructor ; eauto. eapply DomCompute.SSA_path_this_path ; eauto.
  }
  exploit gamma_path_def ; eauto. simpl.
  intros. exploit (H0 x r pc idx) ; eauto.
    
  intros [[HH11 | HH12] | [_ HH2]]. 
  
  congruence.

  elim Hnotin. apply in_rev ; eauto.
  
  elim HH2. 
  split; auto.
Qed.

  
End WT_FUNCTION.
