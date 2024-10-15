Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Dom.
Require Import Op.
Require Import SSA.
Require Import SSAutils.
Require Import Utils.
Require Import CSSA.
Require Import DLib.
Require Import RTLpargen.
Require Import CSSAutils.
Require Import Classical.
Require Import Kildall.
Require Import KildallComp.
Require Import CSSAdef.
Require Import Registers.
Unset Allow StrictProp.

Definition cssaval_ins_spec (get_cssaval : reg -> reg) (ins : instruction) :=
  match ins with
  | Iop Omove (src :: nil) dst _ =>
      get_cssaval src = get_cssaval dst
  | Iop _ _ dst _ =>
      get_cssaval dst = dst
  | Iload _ _ _ dst _ =>
      get_cssaval dst = dst
  | Icall _ _ _ dst _ =>
      get_cssaval dst = dst
  | Ibuiltin _ _ (BR dst) _ =>
      get_cssaval dst = dst
  | _ => True
  end.

Variant cssaval_spec (f : function) (get_cssaval : reg -> reg) : Prop :=
| check_cssaval_spec_intro :
    (forall pc parcb src dst,
      (fn_parcopycode f) ! pc = Some parcb ->
      In (Iparcopy src dst) parcb ->
      get_cssaval dst = get_cssaval src) ->
    (forall pc phib args dst,
      (fn_phicode f) ! pc = Some phib ->
      In (Iphi args dst) phib ->
      get_cssaval dst = dst) ->
    (forall pc ins,
      (fn_code f) ! pc = Some ins ->
      cssaval_ins_spec get_cssaval ins) ->
    (forall param, ext_params f param -> get_cssaval param = param) ->
    cssaval_spec f get_cssaval.

Lemma cssaval_transfer_in_parcopy :
  forall src dst f parcb pc get_cssaval,
  In (Iparcopy src dst) parcb ->
  (fn_parcopycode f) ! pc = Some parcb ->
  cssaval_spec f get_cssaval ->
  get_cssaval dst = get_cssaval src.
Proof.
  intros. inv H1; go.
Qed.

Definition check_cssaval_ins_r
    (elems : list (node * instruction))
    (get_cssaval : reg -> reg) : bool :=
  fold_right
    (fun pcins acc =>
      if negb acc then false
      else match snd pcins with
      | Iop Omove (src :: nil) dst _ =>
          peq (get_cssaval src) (get_cssaval dst)
      | Iop _ _ dst _ =>
          peq (get_cssaval dst) dst
      | Iload _ _ _ dst _ =>
          peq (get_cssaval dst) dst
      | Icall _ _ _ dst _ =>
          peq (get_cssaval dst) dst
      | Ibuiltin _ _ (BR dst) _ =>
          peq (get_cssaval dst) dst
      | _ => true
      end)
    true elems.

Definition check_cssaval_parcb_r
    (parcbs : list (node * parcopyblock))
    (get_cssaval : reg -> reg) : bool :=
  fold_right
    (fun pcparcb acc =>
      if negb acc then false
      else forallb
        (fun parc =>
          match parc with
          | Iparcopy src dst =>
              peq (get_cssaval src) (get_cssaval dst)
          end)
        (snd pcparcb))
    true parcbs.

Definition check_cssaval_phib_r
    (phibs : list (node * phiblock))
    (get_cssaval : reg -> reg) : bool :=
  fold_right
    (fun pcphib acc =>
      if negb acc then false
      else forallb
        (fun phi =>
          match phi with
          | Iphi args dst =>
              peq (get_cssaval dst) dst
          end)
        (snd pcphib))
    true phibs.

Lemma check_cssaval_ins_cons :
  forall elems elt get_cssaval,
  check_cssaval_ins_r (elt :: elems) get_cssaval = true ->
  check_cssaval_ins_r elems get_cssaval = true.
Proof.
  intros. simpl in H.
  destruct (check_cssaval_ins_r elems get_cssaval);
  simpl in H; auto.
Qed.

Lemma check_cssaval_parcb_cons :
  forall pcparcbs elt get_cssaval,
  check_cssaval_parcb_r (elt :: pcparcbs) get_cssaval = true ->
  check_cssaval_parcb_r pcparcbs get_cssaval = true.
Proof.
  intros. simpl in H.
  destruct (check_cssaval_parcb_r pcparcbs get_cssaval);
  simpl in H; auto.
Qed.

Lemma check_cssaval_phib_cons :
  forall pcphibs elt get_cssaval,
  check_cssaval_phib_r (elt :: pcphibs) get_cssaval = true ->
  check_cssaval_phib_r pcphibs get_cssaval = true.
Proof.
  intros. simpl in H.
  destruct (check_cssaval_phib_r pcphibs get_cssaval);
  simpl in H; auto.
Qed.

Lemma check_cssaval_ins_correct_r :
  forall elems get_cssaval,
  check_cssaval_ins_r elems get_cssaval = true ->
  forall pc ins,
  In (pc, ins) elems ->
  cssaval_ins_spec get_cssaval ins.
Proof.
  induction elems; intros; inv H0.
  simpl in *.
  destruct (check_cssaval_ins_r elems get_cssaval).
  simpl in H; auto.
  unfold cssaval_ins_spec.
  flatten H; try destruct peq; go.
  simpl in H. congruence.
  assert (check_cssaval_ins_r elems get_cssaval = true).
  apply check_cssaval_ins_cons with (elt := a); auto.
  eapply IHelems; eauto.
Qed.

Lemma check_cssaval_parcb_correct_r :
  forall pcparcbs get_cssaval,
  check_cssaval_parcb_r pcparcbs get_cssaval = true ->
  forall pc parcb src dst,
  In (pc, parcb) pcparcbs ->
  In (Iparcopy src dst) parcb ->
  get_cssaval src = get_cssaval dst.
Proof.
  induction pcparcbs; intros; inv H0.
  + simpl in *.
    destruct (check_cssaval_parcb_r pcparcbs get_cssaval).
    - simpl in H.
      rewrite forallb_forall in H.
      exploit (H (Iparcopy src dst)); auto.
      intros. destruct peq; go.
    - simpl in H. congruence.
  + simpl in H. 
    assert(check_cssaval_parcb_r pcparcbs get_cssaval = true).
    apply check_cssaval_parcb_cons with (elt := a); auto.
    eapply IHpcparcbs; eauto.
Qed.

Lemma check_cssaval_phib_correct_r :
  forall pcphibs get_cssaval,
  check_cssaval_phib_r pcphibs get_cssaval = true ->
  forall pc phib args dst,
  In (pc, phib) pcphibs ->
  In (Iphi args dst) phib ->
  get_cssaval dst = dst.
Proof.
  induction pcphibs; intros; inv H0.
  + simpl in *.
    destruct (check_cssaval_phib_r pcphibs get_cssaval).
    - simpl in H.
      rewrite forallb_forall in H.
      exploit (H (Iphi args dst)); auto.
      intros. destruct peq; go.
    - simpl in H. congruence.
  + simpl in H. 
    assert(check_cssaval_phib_r pcphibs get_cssaval
      = true).
    apply check_cssaval_phib_cons with (elt := a); auto.
    eapply IHpcphibs; eauto.
Qed.

Lemma check_cssaval_ins_correct :
  forall elems get_cssaval,
  check_cssaval_ins elems get_cssaval = true ->
  check_cssaval_ins_r (rev elems) get_cssaval = true.
Proof.
  intros.
  unfold check_cssaval_ins_r.
  unfold check_cssaval_ins in H.
  rewrite fold_left_rev_right; auto.
Qed.

Lemma check_cssaval_parcb_correct :
  forall pcparcbs get_cssaval,
  check_cssaval_parcb pcparcbs get_cssaval = true ->
  check_cssaval_parcb_r (rev pcparcbs) get_cssaval = true.
Proof.
  intros.
  unfold check_cssaval_parcb_r.
  unfold check_cssaval_parcb in H.
  rewrite fold_left_rev_right; auto.
Qed.

Lemma check_cssaval_phib_correct :
  forall pcphibs get_cssaval,
  check_cssaval_phib pcphibs get_cssaval = true ->
  check_cssaval_phib_r (rev pcphibs) get_cssaval = true.
Proof.
  intros.
  unfold check_cssaval_phib_r.
  unfold check_cssaval_phib in H.
  rewrite fold_left_rev_right; auto.
Qed.

Lemma check_cssaval_correct :
  forall f get_cssaval all_defs ext_params,
  wf_cssa_function f ->
  get_all_def f = all_defs ->
  get_ext_params f all_defs = ext_params ->
  check_cssaval f get_cssaval ext_params = true ->
  cssaval_spec f get_cssaval.
Proof.
  intros until ext_params. intros WF Hdefs Hextparams H.
  constructor; intros; unfold check_cssaval in H;
  repeat rewrite andb_true_iff in H;
  destruct H as [[[Hins Hparcb] Hphib] Hparams].
  + assert (check_cssaval_parcb_r
      (rev (PTree.elements (fn_parcopycode f)))
      get_cssaval = true).
    apply check_cssaval_parcb_correct; auto.
    symmetry. eapply check_cssaval_parcb_correct_r; eauto.
    rewrite <- in_rev.
    eapply PTree.elements_correct; eauto.
  + assert (check_cssaval_phib_r
      (rev (PTree.elements (fn_phicode f)))
      get_cssaval = true).
    apply check_cssaval_phib_correct; auto.
    eapply check_cssaval_phib_correct_r; eauto.
    rewrite <- in_rev.
    eapply PTree.elements_correct; eauto.
  + assert (check_cssaval_ins_r
      (rev (PTree.elements (fn_code f)))
      get_cssaval = true).
    apply check_cssaval_ins_correct; auto.
    eapply check_cssaval_ins_correct_r; eauto.
    rewrite <- in_rev.
    eapply PTree.elements_correct; eauto.
  + unfold check_cssaval_ext_params in *.
    erewrite forallb_forall in Hparams; eauto.
    exploit (Hparams param); auto; intros.
    - rewrite <- InA_In.
      eapply SSARegSet.elements_1; eauto.
      unfold get_ext_params in Hextparams.
      rewrite <- Hextparams.
      inv H0.
      { apply SSARegSet.union_3.
        unfold param_set.
        apply In_fold_right_add1. auto. }
      { apply SSARegSet.union_2.
        apply SSARegSet.diff_3.
        destruct H as [pc Huse].
        eapply search_used_correct; eauto.
        unfold def_set.
        unfold not; intros.
        exploit In_fold_right_add3; eauto.
        intros Hin.
        destruct Hin as [Hin | Hin]. inv Hin.
        contradict Hin. apply none_not_in.
        apply nodef_none; eauto.
      }
    - destruct peq; auto; simpl in H; congruence.
Qed.

(* Utility lemmas about CSSA-value *)

Definition reachable (prog:program) (s:state) :=
  exists s0, exists t, exists s0',
    initial_state prog s0 /\
      glob_capture prog s0 s0'              
      /\  star step (Genv.globalenv prog) s0' t s.

Section PATH.

Variable f : function.
Variable R : reg -> reg.
Hypothesis WF: wf_cssa_function f.
Hypothesis SPEC: cssaval_spec f R.

Inductive path (f : function) : list node -> (@pstate positive) -> Prop :=
    path0 : path f nil (PState (fn_entrypoint f))
  | path1 : forall (p : list node) (pc : positive) 
              (i : instruction) (pc' : node),
            path f p (PState pc) ->
            (fn_code f) ! pc = Some i ->
            reached f pc ->
            In pc' (successors_instr i) -> path f (pc :: p) (PState pc')
  | path2 : forall (p : list node) (pc : positive) (i : instruction),
            path f p (PState pc) ->
            (fn_code f) ! pc = Some i ->
            reached f pc ->
            successors_instr i = nil -> path f (pc :: p) PStop
.

Lemma rev_cons_app_end: forall A (p:list A) a,
  (rev (a::p) = (rev p) ++ a::nil).
Proof.
  induction p; go.
Qed.

Lemma path_dom_path : forall p n,
  path f p n -> Dom.path (cfg f) (exit f) (entry f) (PState (fn_entrypoint f)) (rev p) n.
Proof.
  induction 1 ; eauto. 
  - simpl; go.
  - assert (rev (pc::p) = (rev p) ++ pc::nil) by (eapply rev_cons_app_end; eauto).
    rewrite H3 at 1.
    eapply path_app; eauto.
    econstructor; eauto.
    constructor; eauto; go.
    go. 
  - assert (rev (pc::p) = (rev p) ++ pc::nil) by (eapply rev_cons_app_end; eauto).
    rewrite H3 at 1.
    eapply path_app; eauto.
    econstructor 2; eauto; [idtac| go].
    unfold exit; destruct i; simpl in *; go. 
Qed.

Lemma dom_path_path_aux : forall n1 p n2,
  Dom.path (cfg f) (exit f) (entry f) n1 p n2 ->
  forall p', path f p' n1 -> path f (rev_append p p') n2.
Proof.
  simpl. 
  induction 1; simpl; intros; auto.
  destruct t.
  - simpl.
    inv H.
    inv STEP. inv STEP0.
    econstructor; eauto.
    destruct ((fn_code f) ! pc) eqn: Heq; unfold exit in *; rewrite Heq in *; go.
    econstructor; eauto. flatten NOSTEP; go.
  - apply IHpath.
    destruct s2.
    inv STEP. inv STEP0.
    econstructor; eauto.
    inv STEP.
    destruct ((fn_code f) ! pc) eqn: Heq; unfold exit in *; rewrite Heq in *; go.
    econstructor; eauto. flatten NOSTEP; go. 
Qed.

Lemma dom_path_path : forall p n,
  Dom.path (cfg f) (exit f) (entry f) (PState (entry f)) p n -> path f (rev p) n.
Proof.
  intros.
  generalize (dom_path_path_aux (PState (entry f)) p n H nil).
  rewrite rev_alt; intros.
  apply H0; constructor.
Qed.

Lemma cssaval_path : forall p s,
  path f p s ->
  match s with 
    | PStop => True
    | PState pc =>
      forall r d d', 
        def f r d ->
        def f (R r) d' ->
        (In d p -> In d' p) 
        \/ (d = pc /\ In d' p)
  end.
Proof.
  induction 1; intros; auto.
  left; intros.
  invh In.
  - exploit (IHpath r); eauto.
    inv H3. 
    + assert (HR: R r = r) by (invh cssaval_spec; go).
      rewrite HR in H4. clear HR.
      exploit def_params; eauto. intros.
      assert (d' = fn_entrypoint f) by (eapply def_def_eq; eauto; go); subst; go.
    + invh assigned_code_spec; 
      invh cssaval_spec;
      exploit H7; eauto; intros; simpl in *; flatten H4; try subst; 
      try match goal with 
            | id: R _ = _ ,
              dr: def f (R _) _ |- _ => 
              rewrite id in *;
              assert (EqPC: d' = d) by (eapply def_def_eq ; eauto; go); 
              rewrite EqPC in *; auto
          end.
      assert (use f r0 d) by go.
      exploit exists_def; eauto; intros [d0 Hd0].
      rewrite <- H9 in H4.
      exploit (IHpath r0); eauto.
      intros [CC1|CC2].
      * right. eapply CC1.
        exploit fn_strict; eauto. intros Hdom.
        { invh dom; eauto.
          - invh def; try congruence; normalized.
            + invh assigned_code_spec; allinv; go.
              eelim fn_use_def_code; go.
            + assert (PHI: (fn_phicode f) ! d <> None) by (invh assigned_phi_spec; go). 
              eapply fn_inop_in_jp in PHI; eauto. invh ex; congruence.
          - apply in_rev; eauto.
            apply PATH.
            replace p with (rev (rev p)) by (eapply rev_involutive; eauto).
            eapply path_dom_path; eauto. 
            rewrite rev_involutive; eauto.
        }
      * invh and ; auto.
    + invh assigned_phi_spec; invh ex. 
      assert (HR: R r = r) by (invh cssaval_spec; go). 
      rewrite HR in *. clear HR.
      assert (d = d') by (eapply def_def_eq; eauto; go); subst; go.

    + invh assigned_parcopy_spec; invh ex.
      assert (HR: R r = R x) by (invh cssaval_spec; go).
      rewrite HR in H4.
      assert (use f x d) by go.
      exploit exists_def; eauto; intros [dx Hdx].
      exploit fn_strict; eauto. intros Hdom.
      exploit (IHpath x); eauto.
      { intros [CC1|CC2].
        - invh dom; eauto.
          + inv Hdx; try congruence; normalized.
            * exploit (parcb_inop f WF d); eauto. go.
              intros [s Hs]; invh assigned_code_spec; go.
            * assert (R x = x) by (invh assigned_phi_spec; invh ex; invh cssaval_spec; go). 
              rewrite H8 in H4.
              assert (d' = d) by (eapply def_def_eq; eauto); constructor 1; auto. 
            * eelim fn_strict_use_parcb; go.
          + constructor 2.
            apply CC1.
            rewrite in_rev.                    
            apply PATH.
            eapply path_dom_path; auto.
        - invh and; subst; auto.
      }      
  - exploit (IHpath r); eauto.
    intros [C1|C2].
    + constructor 2; auto.
    + invh and; go.
Qed.
  
End PATH. 

Lemma cssaval_dom : forall f r pc pc' R,
  wf_cssa_function f ->
  cssaval_spec f R ->
  def f (R r) pc ->
  def f r pc' ->
  dom f pc pc'.
Proof.
  intros until R;
  intros WF SPEC DEFR DEFr.
  destruct (peq pc pc').  
  - inv e ; econstructor ; eauto.
  - eelim (classic (dom f pc pc')) ; eauto. intro Hcont.
    eapply not_dom_path_wo in Hcont ; eauto. 
    + destruct Hcont as [p [Hp Hnotin]]. 
      assert (path f (rev p) (PState pc')) by (eapply dom_path_path; eauto).
      exploit (cssaval_path f R); eauto; simpl. intros COR. 
      invh def. 
      * assert (R r = r) by (invh cssaval_spec; go). 
        rewrite H1 in *. clear H1.
        exploit def_params; eauto. intros.
        assert (pc = fn_entrypoint f) by (eapply def_def_eq; eauto; go); subst; go.
      * invh assigned_code_spec; 
        invh cssaval_spec;
        exploit H3; eauto; intros; simpl in *; flatten H3; try subst; 
        try match goal with 
              | id: R _ = _ ,
                dr: def f (R _) _ |- _ => 
                rewrite id in *;
                assert (EqPC: pc = pc') by (eapply def_def_eq ; eauto; go); 
                rewrite EqPC in *; try congruence
            end.
        rewrite <- H5 in DEFR.
        assert (use f r0 pc') by go.
        exploit exists_def; eauto; intros [d0 Hd0].
        exploit fn_strict; eauto. intros Hdom.
        exploit (COR r0); eauto. 
        { intros [C1 | C2].
          - elim Hnotin. 
            eapply in_rev.
            apply C1.
            invh dom; eauto.
            inv Hd0; try congruence; normalized.
            + invh assigned_code_spec; allinv; go.
              eelim fn_use_def_code; go.
            + assert (PHI: (fn_phicode f) ! pc' <> None) by (invh assigned_phi_spec; go). 
              eapply fn_inop_in_jp in PHI; eauto. invh ex; congruence.
            + rewrite <- in_rev. eauto.
          - rewrite <- in_rev in C2. intuition. 
        }

      * invh assigned_phi_spec; invh ex. 
        assert (HR: R r = r) by (invh cssaval_spec; go). 
        rewrite HR in *.
        assert (pc' = pc) by (eapply def_def_eq; eauto; go); congruence.

      * invh assigned_parcopy_spec; invh ex.
        assert (HR: R r = R x) by (invh cssaval_spec; go).
        rewrite HR in DEFR.
        assert (use f x pc') by go.
        exploit exists_def; eauto; intros [d Hd].
        exploit fn_strict; eauto. intros Hdom.
        exploit (COR x); eauto.
        { intros [C1|C2].
          - elim Hnotin. 
            eapply in_rev.
            apply C1.
            invh dom; eauto.
            inv Hd; try congruence; normalized.
            + exploit (parcb_inop f WF pc'); eauto. go.
              intros [s Hs]; invh assigned_code_spec; go.
            + assert (R x = x) by (invh assigned_phi_spec; invh ex; invh cssaval_spec; go). 
              rewrite H4 in DEFR.
              assert (pc = pc') by (eapply def_def_eq; eauto); congruence.
            + eelim fn_strict_use_parcb; go.
            + rewrite <- in_rev; eauto.
          - rewrite <- in_rev in C2; intuition.
        }
    + apply ident_eq.
    + eapply def_reached; eauto.
Qed.

Global Hint Resolve ident_eq: core.

Lemma cssaval_spec_jp_until_phi :
  forall f pc parcb pc' pc'' phib parcb' rs get_cssaval k,
    wf_cssa_function f ->
  cssaval_spec f get_cssaval ->
  (reached f pc) ->
  (fn_parcopycode f) ! pc = Some parcb ->
  (fn_code f) ! pc = Some (Inop pc') ->
  (fn_code f) ! pc' = Some (Inop pc'') ->
  (fn_phicode f) ! pc' = Some phib ->
  (fn_parcopycode f) ! pc' = Some parcb' ->
  (join_point pc' f) ->
  (forall r, ~ assigned_phi_spec (fn_phicode f) pc r) ->
  (~ join_point pc f) ->
  index_pred (get_preds f) pc pc' = Some k ->
  (forall r, cssadom f r pc -> rs # r = rs # (get_cssaval r)) ->

  forall r',
    cssadom f r' pc' ->

    (cssadom f r' pc
     /\ ~ assigned_phi_spec (fn_phicode f) pc' r'
     /\ ~ assigned_parcopy_spec (fn_parcopycode f) pc r'
     /\ ~ assigned_parcopy_spec (fn_parcopycode f) pc' r')

    \/ (assigned_parcopy_spec (fn_parcopycode f) pc r')

    \/ (assigned_phi_spec (fn_phicode f) pc' r')
    ->
    (phi_store k phib (parcopy_store parcb rs)) # r' =
    (phi_store k phib (parcopy_store parcb rs)) # (get_cssaval r').
Proof.
  intros until k.
  intros WF REACH Hcssavalspec Hparcb Hinop Hinop' Hphib
         Hparcb' Hjp Hjp' Hjp'' Hpred Hcssaval r' Hdom Hcases.
  repeat invh or; repeat invh and. 
  - inv Hdom ; try congruence.
    rewrite <- phi_store_other.
    rewrite parcb_other.
    
    * { rewrite <- phi_store_other.
        rewrite parcb_other; auto.
        + intros ; intro; subst.
          assert (def f (get_cssaval r') pc) by go.
          invh cssadom; try congruence ; normalized.
          exploit cssaval_dom; eauto.
          intros.
          contradict H0.
          eapply sdom_not_dom; eauto.
        + intros; intro; subst.
          assert (def f (get_cssaval r') pc') by go.
          exploit cssaval_dom; eauto. intros.
          assert(Hdd: Dom.sdom (cfg f) (exit f) (entry f) def_r def_r).
          eapply sdom_dom_trans ; eauto.
          inv Hdd; go.
      }          
      
    * intros; intro; subst; go.
      eelim H1; go.
      
    * intros; intro; subst; go.
      
  - rewrite <- phi_store_other. 
    
    + invh assigned_parcopy_spec; invh ex; allinv.
      erewrite parcb_store_in; eauto; ssa.
      
      rewrite <- phi_store_other.
      
      * { erewrite parcb_other; eauto.
          - assert (get_cssaval r' = get_cssaval x) by (invh cssaval_spec; go).
            rewrite H.
            eapply Hcssaval; eauto. 
            exploit (exists_def f x pc); eauto; go.
            intros [d Hd].
            econstructor; eauto.
            constructor.
            + exploit (fn_strict f WF x pc); go.
            + intro ; subst.
              invh cssadom; try congruence; normalized; ssa.
              * assert (def_r = pc) by (eapply def_def_eq; eauto; go); subst.
                inv Hd; try congruence; normalized.
                eelim fn_strict_use_parcb with (x:= x); eauto; go.
              * assert (pc' = pc) by (eapply def_def_eq; eauto; go); subst.
                congruence.
              * assert (pc' = pc) by (eapply def_def_eq; eauto; go); subst.
                congruence.
          - exploit (exists_def f x pc); eauto; go. intros [Dx HDx].
            exploit (fn_strict f WF x pc); eauto; go. intros Hdom'.
            intros; intro; subst. 
            eapply dom_eq_sdom in Hdom'. destruct Hdom' as [HdomEQ | Hsdom].
            + invh cssadom; try congruence; normalized; ssa.
              * assert (def_r = pc) by (eapply def_def_eq; eauto; go); subst.
                inv HDx; try congruence; normalized; ssa.
                eelim fn_strict_use_parcb with (x:= x); eauto; go.
              * assert (pc' = pc) by (eapply def_def_eq; eauto; go); subst.
                congruence. 
              * assert (pc' = pc) by (eapply def_def_eq; eauto; go); subst.
                congruence. 
            + assert (get_cssaval r' = get_cssaval x) by (invh cssaval_spec; go).
              rewrite H1 in *.
              exploit (cssaval_dom f x pc Dx); go.
              intros.
              eelim sdom_not_dom; eauto.
            + auto.
        }            
      * intros; intro; subst.
        exploit (cssaval_dom f r' pc' pc) ; eauto; go. 
        intros Hdom'. 
        { invh cssadom; try congruence; normalized.
          - assert (def_r = pc) by (eapply def_def_eq; eauto; go); subst.
            eelim sdom_not_dom; eauto.
          - exploit (wf_cssa_def_phi_parcopy f WF r' pc' pc); eauto; go.
          - assert (pc = pc') by (eapply def_def_eq; eauto; go); subst.
            normalized; eauto.
        }

    + intros; intro; subst; ssa.

  - invh assigned_phi_spec; invh ex; allinv.
    assert (get_cssaval r' = r') by (invh cssaval_spec; go).
    congruence.
Unshelve.
auto.
Qed.

Lemma cssaval_spec_jp :
  forall f pc parcb pc' pc'' phib parcb' rs get_cssaval k,
  wf_cssa_function f ->
  cssaval_spec f get_cssaval ->
  (reached f pc) ->
  (fn_parcopycode f) ! pc = Some parcb ->
  (fn_code f) ! pc = Some (Inop pc') ->
  (fn_code f) ! pc' = Some (Inop pc'') ->
  (fn_phicode f) ! pc' = Some phib ->
  (fn_parcopycode f) ! pc' = Some parcb' ->
  (join_point pc' f) ->
  (forall r, ~ assigned_phi_spec (fn_phicode f) pc r) ->
  (~ join_point pc f) ->
  index_pred (get_preds f) pc pc' = Some k ->
  (forall r, cssadom f r pc ->
    rs # r = rs # (get_cssaval r)) ->
  forall r',
    cssadom f r' pc' ->

    (cssadom f r' pc /\  ~ assigned_phi_spec (fn_phicode f) pc' r')

    \/ (def f r' pc /\ ~ assigned_phi_spec (fn_phicode f) pc r' /\ ~ ext_params f r')
         
    \/ (assigned_phi_spec (fn_phicode f) pc' r' /\ ~ ext_params f r')

    \/ assigned_parcopy_spec (fn_parcopycode f) pc' r' /\ ~ ext_params f r' ->

   (parcopy_store parcb' (phi_store k phib (parcopy_store parcb rs))) !! r' =
   (parcopy_store parcb' (phi_store k phib (parcopy_store parcb rs))) !! (get_cssaval r').
Proof.
  intros until k.
  intros WF REACH Hcssavalspec Hparcb Hinop Hinop' Hphib
         Hparcb' Hjp Hjp' Hjp'' Hpred Hcssaval r' Hdom Hcases.
  repeat invh or; repeat invh and. 
  - inv Hdom ; try congruence.
    + rewrite parcb_other. 
      rewrite parcb_other.
      eapply cssaval_spec_jp_until_phi; go.
      * left.
        { repeat split; auto.
          - intro; invh assigned_parcopy_spec; invh ex; allinv.
            invh cssadom; try congruence; normalized.
            assert (def_r = pc) by (eapply def_def_eq; eauto; go); subst.
            assert (def_r0 = pc) by (eapply def_def_eq; eauto; go); subst.
            inv H5; congruence.            
          - intro; invh assigned_parcopy_spec; invh ex; allinv.
            assert (def_r = pc') by (eapply def_def_eq; eauto; go); subst.
            inv H2; congruence.            
        }
      * intros ; intro; subst.
        assert (def f (get_cssaval r') pc') by go.
        exploit cssaval_dom; eauto. intros.
        exploit (@sdom_dom_trans positive); eauto.
        intros. eelim H6; go. 
      * intros; intro; subst.
        assert (def_r = pc') by (eapply def_def_eq; eauto; go); subst.
        eelim H2; eauto.

    + invh assigned_parcopy_spec; allinv.
      destruct H4 as [src Hsrc].
      erewrite parcb_store_in; eauto; ssa.
      
      assert (get_cssaval r' = get_cssaval src) by (invh cssaval_spec ; go).
      { destruct (classic (assigned_phi_spec (fn_phicode f) pc' src)). 
      
        + assert (HRsrc: get_cssaval src = src)
            by (invh assigned_phi_spec; invh ex; invh cssaval_spec ; go).
          rewrite <- HRsrc. 
          rewrite <- H.
          rewrite parcb_other; auto.
          intros; intro. 
          rewrite HRsrc in *. 
          assert (src = dst) by congruence ; subst. 
          eelim fn_cssa ; eauto ; intros ; repeat invh and ; go.
          specialize (H (get_cssaval r') pc' pc'); repeat invh and. 
          eelim H13; eauto; go.
          
        + erewrite <- phi_store_other with (k := k) (phib := phib)
            by (intros; intro; subst; eelim H3; go).
          rewrite parcb_other; eauto.
          * { erewrite Hcssaval; eauto.
              - rewrite H. 
                assert (use f src pc') by go.
                exploit exists_def ; eauto; intros [d Hd].
                exploit fn_strict ; eauto. intros Hdom.
                apply dom_eq_sdom in Hdom. destruct Hdom as [Hdom | Hdom]; auto.
                + subst. invh def; try congruence; normalized.
                  eelim fn_strict_use_parcb; eauto; go.
                  
                + rewrite parcb_other.
                  * { rewrite <- phi_store_other; eauto.
                      - rewrite parcb_other; auto.
                        intros; intro; subst.
                        
                        assert (def f r' pc') by go. 
                        assert (def f (get_cssaval src) pc) by go. 
                        exploit cssaval_dom; go. intros Hdom''.
                        exploit (@dom_sdom_trans positive) ; eauto. intros.
                        
                        invh cssadom; try congruence; normalized. 
                        assert (def_r = pc') by (eapply def_def_eq ; eauto ; go); subst.
                        eelim elim_sdom_sdom; eauto.
                        
                      - intros; intro; subst.
                        exploit cssaval_dom; go. intros.
                        eelim sdom_not_dom; eauto.
                    }
                    
                  * intros ; intro; subst.
                    exploit cssaval_dom ; go. intros Hdom'.
                    eelim sdom_not_dom; eauto.
                + auto.
              - exploit exists_def; eauto; go.
                intros [d Hd]. 
                econstructor 1; eauto.
                invh cssadom; try congruence; normalized.
                assert (def_r = pc') by (eapply def_def_eq; eauto; go); subst.
                assert (dom f d pc') by (eapply fn_strict; eauto; go).
                constructor.
                eapply dom_sdom_trans; eauto.
                intro; subst. 
                eelim sdom_not_dom; eauto.
            }
          * intros; intro; subst.
            assert (use f dst pc') by go.
            assert (def f dst pc) by go.
            exploit fn_strict ; eauto.
            intros Hdom.
            invh cssadom; try congruence; normalized.
            assert (def_r = pc') by (eapply def_def_eq ; eauto ; go); subst.
            eelim sdom_not_dom; eauto.
      }
          
  - rewrite parcb_other.
    + rewrite parcb_other.
      * eapply cssaval_spec_jp_until_phi; eauto; go.
        right; left; go.
        invh def ; try congruence.
        invh assigned_code_spec; try congruence.
      * intros; intro; subst.
        assert (def f (get_cssaval r') pc') by go.
        exploit cssaval_dom; eauto; go. intros.
        { invh cssadom; ssa.
          - assert (def_r = pc) by (eapply def_def_eq; eauto; go); subst.
            eelim sdom_not_dom; eauto.
          - assert (pc = pc') by (eapply def_def_eq ; eauto; go) ; congruence.
          - assert (pc = pc') by (eapply def_def_eq ; eauto; go) ; congruence. 
        }
    + intros; intro; subst.
      assert (pc = pc') by (eapply def_def_eq ; eauto; go); subst.
      congruence. 
    
  - invh assigned_phi_spec; invh ex ; allinv.
    assert (get_cssaval r' = r') by (invh cssaval_spec; go).
    congruence.

  - invh assigned_parcopy_spec.
    destruct H2 as [src Hsrc]; allinv.
    assert (NoDup (map parc_dst parcb0)) by ssa.
    erewrite parcb_store_in; eauto.      
    assert (get_cssaval r' = get_cssaval src) by (invh cssaval_spec; eauto; go).
    rewrite H0.         
    erewrite parcb_other; eauto.
    
    + eapply cssaval_spec_jp_until_phi; eauto; go.
      * { assert (use f src pc') by go.
          exploit exists_def; eauto; go; intros [d Hd].
          exploit fn_strict; eauto. intros.
          apply dom_eq_sdom in H3. destruct H3 as [C1 | C2].
          - subst.
            invh def ; try congruence; normalized.
            go.
            eelim fn_strict_use_parcb; eauto; go.
          - assert (dom f d pc) by (eapply sdom_dom_pred; go).
            apply dom_eq_sdom in H3. 
            { destruct H3 as [CC1 | CC2].
              - subst; invh def ; try congruence; normalized.
                exploit def_def_eq; eauto; go.
              - econstructor 1; eauto. 
            }
            auto.
          - auto.
        }
        
      * destruct (classic (assigned_phi_spec (fn_phicode f) pc' src)); auto.
        destruct (classic (assigned_parcopy_spec (fn_parcopycode f) pc src)); auto.
        left; repeat split; auto.
        { assert (use f src pc') by go.
          exploit exists_def; eauto; go; intros [d Hd].
          exploit fn_strict; eauto. intros.
          apply dom_eq_sdom in H5. destruct H5 as [C1 | C2].
          - subst.
            invh def ; try congruence; normalized.
            eelim fn_strict_use_parcb; eauto; go.
          - assert (dom f d pc) by (eapply sdom_dom_pred; go).
            apply dom_eq_sdom in H5. 
            { destruct H5 as [CC1 | CC2].
              - subst; invh def ; try congruence; normalized.
              - econstructor 1; eauto. 
            }
            auto.
          - auto.
        }                       
        { intro. eelim fn_strict_use_parcb; eauto; go. }                    
    + intros; intro ; subst.
      assert (use f src pc') by go.
      exploit exists_def ; eauto; go; intros [d Hd].
      exploit fn_strict; eauto. intros Hdom'.
      eapply dom_eq_sdom in Hdom'. 
      { destruct Hdom' as [C1 | C2].
        - subst.
          invh def; normalized.
          + invh assigned_phi_spec; allinv.
            destruct H6 as [args Hargs].
            assert (get_cssaval src = src) by (invh cssaval_spec; eauto).
            assert (get_cssaval r' = get_cssaval src) by (invh cssaval_spec; eauto; go).
            rewrite <- H5 in *.
            rewrite H4 in *.
            eelim fn_strict_use_parcb with (x:= src); eauto; go.
          + eelim fn_strict_use_parcb ; eauto; go.
        - assert (get_cssaval r' = get_cssaval src) by (invh cssaval_spec; eauto; go).
          rewrite H4 in *.
          exploit cssaval_dom; eauto; go. intros.
          eelim sdom_not_dom; eauto. 
      }
      auto.
Qed.

Definition cssaval (f: function) : reg -> reg :=
  let cssaval := compute_cssaval_function f in
  if (check_cssaval f cssaval (get_ext_params f (get_all_def f)))
  then cssaval
  else (fun r => r).

Lemma cssaval_correct : forall f, 
    wf_cssa_function f ->
    cssaval_spec f (cssaval f) \/ (cssaval f = fun r => r).
Proof.
  unfold cssaval; intros; flatten; simpl; go.
  left. eapply check_cssaval_correct; eauto.
Qed.

Variant sf_inv (ge: genv) : stackframe -> Prop :=
  | sf_inv_intro: forall res f sp pc rs pred sig ros args
    (WFF: wf_cssa_function f)
    (REACHED: reached f pc)
    (SFINV: forall r,
                cssadom f r pc ->
                r <> res ->
                rs # r = rs # (cssaval f r))
    (SINS: (fn_code f) ! pred = Some (Icall sig ros args res pc)),
    sf_inv ge (Stackframe res f sp pc rs).
Global Hint Constructors sf_inv: core.

Inductive sfl_inv (ge: genv) : list stackframe -> Prop :=
| sfl_nil : sfl_inv ge nil
| sfl_cons : forall s sl,
               sf_inv ge s ->
               sfl_inv ge sl ->
               sfl_inv ge (s::sl).

Variant s_inv (ge: genv) : state -> Prop :=
  | si_State : forall s f sp pc rs m
    (WFF: wf_cssa_function f)
    (REACHED: reached f pc)
    (SINV: forall r, cssadom f r pc -> rs # r = rs # (cssaval f r))
    (SFINV: sfl_inv ge s),
    s_inv ge (State s f sp pc rs m)
  | si_Callstate : forall s f args m
    (WFF: wf_cssa_fundef f)
    (SFINV: sfl_inv ge s),
    s_inv ge (Callstate s f args m)
  | si_Returnstate: forall s v m
    (SFINV: sfl_inv ge s),
    s_inv ge (Returnstate s v m).

Global Hint Constructors s_inv: core.

Section INV.

Variable prog : program.
Hypothesis HWF: wf_cssa_program prog.
Let ge_prog := Genv.globalenv prog.

Lemma wf_cssa_prog_find_function: forall ros rs fd, 
  find_function ge_prog ros rs = Some fd ->
  wf_cssa_fundef fd.
Proof.
  intros.
  assert (ID: exists id, In (id, Gfun fd) (prog_defs prog)).
  unfold find_function, Genv.find_funct in *.
  flatten H8; apply Genv.find_funct_ptr_inversion with (b := b); auto.
  destruct ID as [id Infd].
  apply HWF with id; auto.
Qed.

Lemma s_inv_initial : forall s,
  initial_state prog s ->
  s_inv ge_prog s.
Proof.
  intros. inv H. econstructor ; eauto.
  generalize HWF ; intro Hwf.
  eapply Genv.find_funct_ptr_prop ; eauto.
  econstructor; eauto.
Qed.

Lemma s_inv_initial_capture : forall s s',
  initial_state prog s ->
  glob_capture prog s s' -> 
  s_inv ge_prog s'.
Proof.
  intros. exploit s_inv_initial; eauto. intros.
  inv H. inv H0. inv H1. econstructor; eauto.
Qed.

Lemma subj_red : forall s s' t,
  s_inv ge_prog s ->
  step ge_prog s t s' ->
  s_inv ge_prog s'.
Proof.
  intros s s' t HINV STEP.
  inv HINV.
  - inv STEP ; eauto. 
    
    + constructor; auto; go. 
      intros. 
      edestruct (cssaval_correct f) as [SPEC| ID]; auto; [idtac| rewrite ID; auto].
      exploit (dsd_pred_not_join_point f WFF pc pc'); eauto; go.
      { intros; repeat invh or ; repeat invh and; auto.
        - assert (cssaval f r = r) by (invh cssaval_spec; go).
          congruence. 
        - invh assigned_code_spec; congruence.
      } 

    + constructor; auto; go.
      intros. exploit (dsd_pred_njp f WFF pc pc'); eauto.
      { intro Hcont; subst; normalized. }
      { go. }
      intros Hjp.
      assert (exists pc'', (fn_code f) ! pc' = Some (Inop pc'')).
      { eapply fn_phicode_inv in H8; eauto. 
        eapply fn_inop_in_jp in H8; eauto.
      }
      invh ex.
      edestruct (cssaval_correct f) as [SPEC| ID]; auto; [idtac| rewrite ID; auto].
      eapply cssaval_spec_jp; eauto; normalized.
      { intros; intro. 
        invh assigned_phi_spec; invh ex; allinv.
        exploit (jp_not_preceded_by_jp f WFF pc pc'); eauto; go.
      }      

    + (* Iop *) 
      constructor; auto; go. 
      intros. 
      edestruct (cssaval_correct f) as [SPEC| ID]; auto; [idtac| rewrite ID; auto].
      assert (JP:= not_nop_not_jp f WFF pc); flatten JP.
      assert (JP2:= not_nop_not_jp_2 f WFF pc); flatten JP2.
      exploit (dsd_pred_not_join_point f WFF pc pc'); eauto; go.
      { intros; repeat invh or ; repeat invh and; auto.
        - assert (cssaval f r = r) by (invh cssaval_spec ; go).
          congruence. 
        - rewrite PMap.gso; eauto. 
          rewrite PMap.gso; eauto. 
          * intro. subst. 
            invh cssadom; try congruence; normalized.
            assert (dom f pc def_r) by (eapply cssaval_dom; eauto; go).
            eelim sdom_not_dom; eauto.
          * intro. subst. eelim H2; go.
        - destruct (peq r (cssaval f r)) as [EQ|EQ]; [ rewrite <- EQ ; auto | idtac]. 
          invh assigned_code_spec; allinv.
          match goal with 
            | id: (fn_code f) ! pc = Some ?i |- _ => 
              assert (cssaval_ins_spec (cssaval f) i) 
                by (invh cssaval_spec; eauto; go)
          end.
          simpl in H1. flatten H1 ; subst; eauto.
          rewrite PMap.gss.
          rewrite <- H1.
          rewrite PMap.gso; try congruence.
          inv H8. 
          eapply SINV; eauto.
          exploit exists_def; go; intros [d Hd].
          exploit fn_strict; eauto; go ; intros Hdom.
          econstructor 1; eauto.
          constructor; go.
          intro; subst; eelim fn_use_def_code; go.
          invh def ; try congruence; normalized; ssa.
      }

    + (* Iload *) 
      constructor; auto; go. 
      intros. 
      edestruct (cssaval_correct f) as [SPEC| ID]; auto; [idtac| rewrite ID; auto].
      assert (JP:= not_nop_not_jp f WFF pc); flatten JP.
      assert (JP2:= not_nop_not_jp_2 f WFF pc); flatten JP2.
      exploit (dsd_pred_not_join_point f WFF pc pc'); eauto; go.
      { intros; repeat invh or ; repeat invh and; auto.
        - assert (cssaval f r = r) by (invh cssaval_spec ; go).
          congruence. 
        - rewrite PMap.gso; eauto. 
          rewrite PMap.gso; eauto. 
          * intro. subst. 
            invh cssadom; try congruence; normalized.
            assert (dom f pc def_r) by (eapply cssaval_dom; eauto; go).
            eelim sdom_not_dom; eauto.
          * intro. subst. eelim H2; go.
        - destruct (peq r (cssaval f r)) as [EQ|EQ]; [ rewrite <- EQ ; auto | idtac]. 
          invh assigned_code_spec; allinv.
          match goal with 
            | id: (fn_code f) ! pc = Some ?i |- _ => 
              assert (cssaval_ins_spec (cssaval f) i) 
                by (invh cssaval_spec; eauto; go)
          end.
          simpl in H1. flatten H1 ; subst; eauto.
      } 

    + (* Istore *) 
      constructor; auto; go. 
      intros. 
      edestruct (cssaval_correct f) as [SPEC| ID]; auto; [idtac| rewrite ID; auto].
      assert (JP:= not_nop_not_jp f WFF pc); flatten JP.
      assert (JP2:= not_nop_not_jp_2 f WFF pc); flatten JP2.
      exploit (dsd_pred_not_join_point f WFF pc pc'); eauto; go.
      { intros; repeat invh or ; repeat invh and; auto.
        - assert (cssaval f r = r) by (invh cssaval_spec ; go).
          congruence. 
        - destruct (peq r (cssaval f r)) as [EQ|EQ]; [ rewrite <- EQ ; auto | idtac]. 
          invh assigned_code_spec; allinv.
      } 

    + (* Icall *)
      constructor. 
      * 
        eapply wf_cssa_prog_find_function; eauto.
      * constructor; auto. 
        econstructor; go. 
        intros.
        edestruct (cssaval_correct f) as [SPEC| ID]; auto; [idtac| rewrite ID; auto].
        assert (JP:= not_nop_not_jp f WFF pc); flatten JP.
        assert (JP2:= not_nop_not_jp_2 f WFF pc); flatten JP2.
        exploit (dsd_pred_not_join_point f WFF pc pc'); eauto; go.
        { intros; repeat invh or ; repeat invh and; auto.
          - assert (cssaval f r = r) by (invh cssaval_spec ; go).
            congruence. 
          - destruct (peq r (cssaval f r)) as [EQ|EQ]; [ rewrite <- EQ ; auto | idtac]. 
            invh assigned_code_spec; allinv. congruence.
        } 

    + (* Itailcall *)
      constructor; auto.
      eapply wf_cssa_prog_find_function; eauto. 

    + (* Ibuiltin *) 
      constructor; auto; go. 
      intros. 
      edestruct (cssaval_correct f) as [SPEC| ID]; auto; [idtac| rewrite ID; auto].
      assert (JP:= not_nop_not_jp f WFF pc); flatten JP.
      assert (JP2:= not_nop_not_jp_2 f WFF pc); flatten JP2.
      exploit (dsd_pred_not_join_point f WFF pc pc'); eauto; go.
      { intros; repeat invh or ; repeat invh and; auto.
        - assert (cssaval f r = r) by (invh cssaval_spec ; go).
          congruence. 
        - destruct res ; try eauto. simpl. rewrite PMap.gso; eauto. 
          rewrite PMap.gso; eauto. 
          * intro. subst. 
            invh cssadom; try congruence; normalized.
            assert (dom f pc def_r) by (eapply cssaval_dom; eauto; go).
            eelim sdom_not_dom; eauto.
          * intro. subst. eelim H2; go.
        - destruct (peq r (cssaval f r)) as [EQ|EQ]; [ rewrite <- EQ ; auto | idtac]. 
          invh assigned_code_spec; allinv.
          match goal with 
            | id: (fn_code f) ! pc = Some ?i |- _ => 
              assert (cssaval_ins_spec (cssaval f) i) 
                by (invh cssaval_spec; eauto; go)
          end.
          simpl in H1. flatten H1 ; subst; eauto.
      } 

    + (* Icond true *) 
      constructor; auto; go. 
      intros. 
      edestruct (cssaval_correct f) as [SPEC| ID]; auto; [idtac| rewrite ID; auto].
      assert (JP:= not_nop_not_jp f WFF pc); flatten JP.
      assert (JP2:= not_nop_not_jp_2 f WFF pc); flatten JP2.
      exploit (dsd_pred_not_join_point f WFF pc ifso); eauto; go.
      { intros; repeat invh or ; repeat invh and; auto. }
      { intros; repeat invh or ; repeat invh and; auto.
        - assert (cssaval f r = r) by (invh cssaval_spec ; go).
          congruence. 
        - destruct (peq r (cssaval f r)) as [EQ|EQ]; [ rewrite <- EQ ; auto | idtac]. 
          invh assigned_code_spec; allinv.
      }
      
    + (* Icond false *) 
      constructor; auto; go. 
      intros. 
      edestruct (cssaval_correct f) as [SPEC| ID]; auto; [idtac| rewrite ID; auto].
      assert (JP:= not_nop_not_jp f WFF pc); flatten JP.
      assert (JP2:= not_nop_not_jp_2 f WFF pc); flatten JP2.
      exploit (dsd_pred_not_join_point f WFF pc ifnot); eauto; go.
      { intros; repeat invh or ; repeat invh and; auto. }
      { intros; repeat invh or ; repeat invh and; auto.
        - assert (cssaval f r = r) by (invh cssaval_spec ; go).
          congruence. 
        - destruct (peq r (cssaval f r)) as [EQ|EQ]; [ rewrite <- EQ ; auto | idtac]. 
          invh assigned_code_spec; allinv.
      }

    + (* Ijumptable *) 
      constructor; auto. 
      { eapply Relation_Operators.rt_trans; eauto.
        constructor.
        econstructor; eauto.
        simpl; eauto using list_nth_z_in. 
      }
      intros. 
      edestruct (cssaval_correct f) as [SPEC| ID]; auto; [idtac| rewrite ID; auto].
      assert (JP:= not_nop_not_jp f WFF pc); flatten JP.
      assert (JP2:= not_nop_not_jp_2 f WFF pc); flatten JP2.
      assert (cfg f pc pc').
      { econstructor; eauto.
        simpl; eauto using list_nth_z_in. 
      }
      exploit (dsd_pred_not_join_point f WFF pc pc'); eauto; go.
      { eapply JP; eauto using list_nth_z_in. }
      { intros; repeat invh or ; repeat invh and; auto.
        - assert (cssaval f r = r) by (invh cssaval_spec ; go).
          congruence. 
        - destruct (peq r (cssaval f r)) as [EQ|EQ]; [ rewrite <- EQ ; auto | idtac]. 
          invh assigned_code_spec; allinv.
      }     

  - (* Function start *) 
    invh step; go.
    invh wf_cssa_fundef; auto. 
    constructor; auto.
    + go.
    + intros.
      exploit cssadom_entry; go.

  - invh step; go. 
    invh sfl_inv.
    invh sf_inv.
    constructor; auto.
    intros.
    edestruct (cssaval_correct f) as [SPEC| ID]; auto; [idtac| rewrite ID; auto].
    exploit (dsd_pred_not_join_point f WFF pred); eauto.
    { exploit fn_code_reached; eauto. }
    { econstructor; go. }
    { intro. eapply (fn_normalized f WFF pc pred) in H0.
      congruence.
      unfold successors, successors_list; simpl.
      rewrite PTree.gmap1; rewrite SINS; unfold option_map, successors_instr; flatten; 
      auto.
    }
    { intros; repeat invh or ; repeat invh and; auto.
      - assert (cssaval f r = r) by (invh cssaval_spec ; go).
        congruence. 
      - assert (r <> res) by (intro; subst; eelim H3; eauto). 
        rewrite PMap.gso; auto.
        rewrite SFINV; eauto.
        rewrite PMap.gso; auto.
        intro. 
        assert (def f (cssaval f r) pred) by go.
        invh cssadom.
        + exploit cssaval_dom; eauto.
          intros. eelim sdom_not_dom; eauto.
        + invh assigned_phi_spec; invh ex.
          exploit (fn_inop_in_jp f WFF pred); eauto; go.
          intros; invh ex; congruence.          
        + invh assigned_parcopy_spec; invh ex; 
          exploit (parcb_inop f WFF pred); eauto. go.
          intros [n Hn]. congruence. 
      - destruct (peq r (cssaval f r)) as [EQ|EQ]; [ rewrite <- EQ ; auto | idtac]. 
        invh assigned_code_spec; allinv.
        assert (cssaval f r = r) by (invh cssaval_spec; exploit H5; eauto). 
        rewrite H1; auto.
    }     
Qed.    
      
Lemma ssa_inv1_aux : forall s s' t,
  s_inv ge_prog s ->
  star step ge_prog s t s' ->
  s_inv ge_prog s'.
Proof.
  induction 2 ; intros.
  auto.
  eapply IHstar ; eauto.
  eapply subj_red ; eauto.
Qed.

Theorem ssa_inv1 : forall s s0 s' t,
  initial_state prog s ->
  glob_capture prog s s0 ->  
  star step ge_prog s0 t s' ->
  s_inv ge_prog s'.
Proof.
  intros.
  eapply ssa_inv1_aux ; eauto.
  eapply s_inv_initial_capture ; eauto.
Qed.

Lemma cssaval_spec_correct :
  forall f r pc s sp rs m,
  reachable prog (State s f sp pc rs m) ->
  cssadom f r pc ->
  rs # r = rs # (cssaval f r).
Proof.
  intros.
  destruct H as [s0 [t [IS Hstar]]].
  destruct Hstar as [s0' [ICAP Hstar]].
  eapply ssa_inv1 in Hstar; eauto.
  invh s_inv; go.
Qed.

Lemma cssaval_spec_correct_2 :
  forall f r1 r2 pc s sp rs m,
  cssadom f r1 pc ->
  cssadom f r2 pc ->
  cssaval f r1 = cssaval f r2 ->
  reachable prog (State s f sp pc rs m) ->
  rs # r1 = rs # r2.
Proof.
  intros.
  erewrite cssaval_spec_correct; eauto.
  symmetry. erewrite cssaval_spec_correct; eauto.
  congruence.
Qed.

End INV.
