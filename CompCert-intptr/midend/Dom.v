Require Import Coqlib.
Require Import Maps.
Require Import Classical.

Require Import Utils.
Require Import Relation_Operators.
Require Import Relations.Relation_Definitions.
Require Import DLib.

Unset Allow StrictProp.

(** * Formalization of Dominators *)

(** We formalize dominators on top of an abstract notion of graph,
 parameterized by the [node] type, on which we assume a decidable
 equality. In the CompCertSSA middle-end, [node] is [positive]. *)

Section Graph.  
  Context {node : Type}.
  Variable peq : forall x y:node, {x=y}+{x<>y}.

  Variable cfg : node -> node -> Prop.
  Variable exit : node -> Prop.
  Variable entry : node.

  (** [reached pc] holds if node [pc] is reachable from [entry] *)
  Definition reached (pc: node) : Prop :=  (cfg **) entry pc.  
  
  (** Definition of paths in the CFG of a function *)

  Variant pstate : Type :=
  | PState: forall (pc: node), pstate
  | PStop: pstate.
  
  Variant path_step : pstate -> node -> pstate -> Prop :=
  | step_i: forall pc pc'
    (CFG : reached pc)
    (STEP: cfg pc pc'), 
    path_step (PState pc) pc (PState pc')
  | step_stop: forall pc
    (CFG : reached pc)
    (NOSTEP : exit pc),
    path_step (PState pc) pc PStop.
  
  Inductive path : pstate -> list node -> pstate -> Prop :=
  | path_refl : forall s,  path s nil s  
  | path_cons : forall s1 t s2 pc s3 
    (STEP: path_step s1 pc s2)
    (PATH: path s2 t s3),
    path s1 (pc::t) s3.  
  Hint Constructors path_step path: core.

  (** Useful lemmas about [path] *)
  Lemma path_app : forall p1 s1 s2 s3 p2, 
    path s1 p1 s2 ->
    path s2 p2 s3 ->
    path s1 (p1++p2) s3.
  Proof.
    induction p1; intros. 
    inv H. simpl ; auto.
    simpl.
    inv H.
    econstructor ; eauto.
  Qed.   

  Lemma path_from_ret_nil : forall p s,
    path PStop p s ->  p = nil.
  Proof.
    induction p ; intros. auto.
    inv H ; auto.
    inv STEP.
  Qed.
  
  Lemma in_path_split : forall (pc pc' pc'' : node) (p : list node),
    path (PState pc) p (PState pc') ->
    In pc'' p ->
    exists p' : list node,
      exists p'' : list node,
        path (PState pc) p' (PState pc'') /\
        ~ In pc'' p' /\ 
        path (PState pc'') (pc'' :: p'') (PState pc').
  Proof.
    induction 1 ; intros.
    - inv H.
    - inv STEP.  
      destruct (peq pc'' pc0). 
      inv e. 
      exists nil ; exists t ; split ; (econstructor ; eauto).

      inv H0. congruence. 
      exploit IHpath ; eauto.  intros [p' [p'' [Hp' [Hnotin Hp'']]]].
      
      exists (pc0::p').    
      exists p''.
      split.
      econstructor 2 ; eauto. 
      econstructor ; eauto.
      intro Hcont ; inv Hcont ; intuition. 

      exploit path_from_ret_nil ; eauto. intros Heq. inv Heq. inv H0. 
      inv H. exists nil; exists nil. 
      split; (econstructor ; eauto).
      inv H2.
  Qed.

  Lemma in_path_split_app : forall pc pc' pc'' p, 
    path (PState pc) p (PState pc') ->
    In pc'' p ->
    exists p', exists p'', 
      path (PState pc) p' (PState pc'')
      /\ ~ In pc'' p'
      /\ p = p'++(pc''::p'').
  Proof.
    induction 1 ; intros.
    inv H.

    inv STEP.  
    destruct (peq pc'' pc0). 
    inv e. clear H0.   
    exists nil. exists t ; split ; econstructor ; eauto.
    
    inv H0. congruence. 
    exploit IHpath ; eauto.  intros [p' [p'' [Hp' [Hnotin Happ]]]].
    rewrite Happ.
    
    exists (pc0::p').    
    exists p''.
    split.
    econstructor 2 ; eauto. 
    split. intro Hcont. inv Hcont. elim n ; auto. elim Hnotin ; auto. 
    simpl ; auto.

    exploit path_from_ret_nil ; eauto. intros. inv H1. inv H.
    inv H0. exists nil. exists nil. split.
    econstructor ; eauto.
    split ; auto.
    elim H.
  Qed.      

  Lemma cfg_path : forall pc pc', 
    cfg** pc pc' -> reached pc -> exists p, path (PState pc) p (PState pc'). 
  Proof.
    intros pc pc' HCFG. 
    eapply (clos_refl_trans_ind node) with 
      (P :=  fun a b => 
               reached a -> exists p, path (PState a) p (PState b)) ; eauto; intros.    
    clear pc pc' HCFG.

    exploit H0; eauto; intros [pxy Hpxy].
        
    assert (reached y). eapply rt_trans ; eauto.
    exploit H2 ; eauto ; intros [pyz Hpyz].
    exists (pxy++pyz). eapply path_app; eauto. 
  Qed.
  
  Lemma reached_path : forall pc', 
    reached pc' -> exists p, path (PState entry) p (PState pc').
  Proof.
    intros.
    apply cfg_path; auto.
    eapply rt_refl ; eauto.  
  Qed.  

  (** Dominance relation: [dom pc pc'] holds if node [pc] dominates node [pc'] *)
  Variant dom : node -> node -> Prop :=
  | dom_eq : forall pc, dom pc pc
  | dom_path : forall pc pc'
    (RPC' : reached pc') 
    (PATH : forall p, path (PState entry) p (PState pc') -> In pc p), 
    dom pc pc'.
  Hint Constructors dom: core.
  
  (** Dominance relation is reflexive *)
  Lemma dom_refl : forall pc, dom pc pc.
  Proof.
    intros ; eauto.
  Qed.

  (** Dominance relation is transitive *)
  Lemma dom_trans : forall pc1 pc2 pc3, 
    dom pc1 pc2 -> dom pc2 pc3 -> dom pc1 pc3.
  Proof.
    intros; inv H; auto. 
    inv H0. econstructor ; eauto. 
    
    econstructor ; eauto ; intros.
    exploit PATH0 ; eauto ; intros.
    
    destruct (peq entry pc2). 
    inv e. eelim (PATH nil) ; eauto.  

    exploit in_path_split_app ; eauto.
    intros. destruct H1 as [p1 [p2 [Hpath [Htrace Happ]]]].
    
    inv Happ.
    exploit PATH ; eauto.
    intros. eapply in_app ; eauto.
  Qed.  

  (** Strict dominance [sdom pc pc'] holds if [pc] strictly dominates [pc'] *)
  Inductive sdom (pc pc' : node) : Prop := 
    | sdom_intro : forall (DOM : (dom pc pc')) (NEQ : pc <> pc'), sdom pc pc'.

  (* Useful lemmas about [sdom] and [dom] *)
  Lemma sdom_spec : forall pc1 pc2, sdom pc1 pc2 -> (dom pc1 pc2) /\ pc1 <> pc2.
  Proof. 
    intros. inv H ; auto.
  Qed.
  
  Lemma not_sdom_spec : forall pc1 pc2, ~ sdom pc1 pc2 -> 
    (pc1 = pc2) \/ (~ dom pc1 pc2).
  Proof.
    intros.
    destruct (peq pc1 pc2).
    auto.
    right.
    intro Hcont.
    elim H ; auto. econstructor ; eauto.
   Qed.  

  Lemma sdom_not_dom : forall pc pc', sdom pc pc' -> ~ dom pc' pc.
  Proof.
    intros pc pc' SDOM.  
    inv SDOM.
    generalize DOM ; inv DOM ; intros DOM.
    congruence.

    exploit reached_path ; eauto. intros [ppc' Hppc'].
    exploit PATH ; eauto. intros.
    
    exploit in_path_split ; eauto. 
    intros [p' [p'' [Hp' [Hnotin Happ]]]]. 
    
    destruct (In_dec peq pc' p').
    
    exploit (in_path_split_app entry pc); eauto. 
    intros [p2 [p3 [Hp'' [Hnotin' Happ']]]]. inv Happ'.
    exploit PATH ; eauto. intros.
    elim Hnotin. eapply in_app ; eauto.

    intro Hcont. inv Hcont. congruence.
    exploit PATH0 ; eauto.    
  Qed.

  (** Dominance relation is antisymmetric *)
  Lemma dom_antisym : forall pc pc',
    dom pc pc' ->
    dom pc' pc ->
    pc = pc'.
  Proof.
    intros. case (peq pc pc') ; intros. 
    auto. 
    exploit sdom_not_dom ; eauto. 
    split ; auto.
    intuition.       
  Qed.

  (** Strict dominance is transitive *)
  Lemma sdom_trans : forall pc1 pc2 pc3,
    sdom pc1 pc2 -> sdom pc2 pc3 -> sdom pc1 pc3.
  Proof.
    intros.
    inv H. inv H0. 
    econstructor ; eauto.
    eapply dom_trans; eauto.
    intro Hcont. inv Hcont. 
    exploit dom_antisym ; eauto.
  Qed.

  Lemma dom_sdom_trans : forall pc1 pc2 pc3,
    dom pc1 pc2 -> sdom pc2 pc3 -> sdom pc1 pc3.
  Proof.
    intros.
    destruct (peq pc1 pc2).
    inv e. auto. 
    eapply sdom_trans; eauto.  
    econstructor ; eauto.
  Qed.

  (** Dominance relation is an order *)
  Lemma dom_order : order node dom.
  Proof.
    constructor.
    exact dom_refl. 
    exact dom_trans. 
    exact dom_antisym.
  Qed.

  (** Other utility lemmas about (strict) dominance *)
  Lemma sdom_dom_pred : forall pc pc' pc'', 
    sdom pc pc'' ->
    reached pc' ->
    cfg pc' pc'' ->
    dom pc pc'.
  Proof.
    intros.
    destruct (peq pc pc').
    - inv e ; econstructor ; eauto.
    
    - econstructor ; eauto.    
      intros. inv H. inv DOM; try congruence.
      exploit (PATH (p++(pc'::nil))).
      + eapply path_app; eauto.
      + rewrite in_app_iff; destruct 1; auto.
        simpl in H; destruct H; intuition.
  Qed.    

  Lemma dom_eq_sdom : forall pc pc', 
    dom pc pc' -> 
    pc = pc' \/ sdom pc pc'.
  Proof.
    intros.
    destruct (peq pc pc').
    inv e ; auto.
    right. inv H. congruence. constructor ; auto.
  Qed.

  Lemma entry_dom : forall pc, 
    reached pc ->
    dom entry pc.
  Proof.
    intros.
    destruct (peq pc entry). inv e ; constructor ; auto.
    constructor; auto.
    intros.  
    inv H0. congruence.
    inv STEP ; eauto with datatypes.
  Qed.

  Lemma dom_entry : forall pc, 
    dom pc entry ->
    pc = entry.
  Proof.
    intros.
    destruct (peq pc entry). inv e ; constructor ; auto.
    
    inv H. congruence.
    exploit (PATH nil) ; eauto.
    intros. inv H.
  Qed.
  
  Lemma entry_sdom : forall pc, 
    ~ sdom pc entry.
  Proof.
    intros.
    intro Hcont.
    inv Hcont. 
    exploit dom_entry ; eauto.
  Qed.   


  Lemma not_dom_path_wo : forall pc pc', 
    ~ dom pc pc' ->
    reached pc' ->
    (exists p, path (PState entry) p (PState pc') /\ ~ In pc p).
  Proof.
    intros.
    destruct (peq pc pc').
    inv e. elim H ; econstructor ; eauto.
    eelim (classic (exists p, path  (PState entry) p (PState pc') /\ ~ In pc p)); intros. 
    eauto. 
    elim H. econstructor ; eauto.
    intros.
    destruct (In_dec peq pc p);  auto.
    eelim H1. exists p ; eauto.
  Qed.

  Lemma sdom_dom_trans : forall pc1 pc2 pc3,
                           sdom pc1 pc2 -> dom pc2 pc3 -> sdom pc1 pc3.
  Proof.
    intros.
    destruct (peq pc2 pc3).
    - go. 
    - eapply sdom_trans; go.  
  Qed.

  Lemma elim_sdom_sdom : forall pc1 pc2, 
                           sdom pc1 pc2 -> sdom pc2 pc1 -> False.
  Proof.
    intros; repeat invh sdom.
    exploit dom_antisym; eauto.
  Qed.

End Graph.
