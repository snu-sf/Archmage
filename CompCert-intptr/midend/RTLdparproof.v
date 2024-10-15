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
Require Import PointerOp Simulation RTLparD RTLD sflib.
Require Import Smallstep.
Require Import RTL.
Require Import SSA.
Require Import SSAutils.
Require Import CSSA.
Require Import RTLdparspec.
Require Import Kildall.
Require Import Conventions.
Require Import Utils.
Require Import NArith.
Require Import Events.
Require Import Permutation.
Require Import DLib.
Require Import CSSAproof.
Require Import RTLpar.
Require Import RTLdpar.
Require Import Classical.
From Paco Require Import paco.

Lemma max_reg_correct_code: forall f,
    Ple (CSSAgen.get_max_reg_in_code (RTLpar.fn_code f))
        (get_maxreg f).
Proof.
  intros.
  unfold get_maxreg.
  eapply Pos.le_max_l; eauto.
Qed.

Notation no_fresh :=  (fun f => Parmov.is_not_temp reg (fun _ : reg => (fresh_init f))).

Lemma get_maxreg_is_not_temp_code : 
  forall f pc, 
    match (fn_code f) ! pc with 
      | None => True 
      | Some ins => 
          match ins with 
            | SSA.Inop s => True 
            | SSA.Iop op args dst s => 
              forall r, In r (dst::args) -> no_fresh f r  
            | SSA.Iload ch ad args dst s => 
              forall r, In r (dst::args) -> no_fresh f r  
            | SSA.Istore ch ad args src s => 
              forall r, In r (src::args) -> no_fresh f r  
            | SSA.Icall sig ros args dst s =>
              match ros with 
                | inl rf => forall r, In r (rf::dst::args) -> no_fresh f r  
                | inr _ => forall r, In r (dst::args) -> no_fresh f r  
              end
            | SSA.Itailcall sig ros args => 
              match ros with 
                | inl rf => forall r, In r (rf::args) -> no_fresh f r  
                | inr _ => forall r, In r args -> no_fresh f r  
              end
            | SSA.Ibuiltin ef args dst s => 
              forall r, In r ((params_of_builtin_res dst) ++ (params_of_builtin_args args)) -> no_fresh f r  
            | SSA.Icond cond args ifso ifnot => 
              forall r, In r args -> no_fresh f r  
            | SSA.Ijumptable arg tbl => 
              no_fresh f arg  
            | SSA.Ireturn rop => 
              match rop with 
                | Some r => no_fresh f r
                | _ => True
              end
          end
    end.
Proof.
  unfold fresh_init, Parmov.is_not_temp.
  intros. flatten; subst; auto;
  try solve [ 
    match goal with 
      | |- forall r, _  => intros rr Hin _  
      | |- _ => intros _
    end;
    intro Hcont ; first [ inv Hcont|  subst];
    assert (Hple:= max_reg_correct_code f);
    rewrite <- Pos.lt_succ_r in Hple;
    eapply max_reg_in_code in Eq; eauto; simpl in *;
    try invh or; 
      (exploit Pos.le_lt_trans; eauto; intros Hlt;
      eapply Pos.lt_nle  in Hlt;
      elim Hlt;
      eapply max_reg_in_list_correct; eauto)
      ].
Qed.    

Lemma max_reg_correct_parccode : forall f,
  Ple (get_max_reg_in_parcode (fn_parcopycode f)) (get_maxreg f).
Proof.
  intros.
  unfold get_maxreg.
  eapply Ple_trans ; eauto.
  apply Pos.le_max_l.
  eapply Pos.le_max_r.
Qed.

Lemma ple_foldmaxparcb_init :
  forall l m n,
  Ple m n ->
  Ple
    m
    (List.fold_left
      (fun m (pparcb : positive * parcopyblock) => Pos.max m
        (get_max_reg_in_parcb (snd pparcb)))
      l n).
Proof.
  induction l; intros.
  simpl. auto.
  simpl.
  eapply Ple_trans with
    (Pos.max m (get_max_reg_in_parcb (snd a))); auto.
  apply Pos.le_max_l.
  apply IHl.
  apply Pos.max_le_compat.
  auto. apply Ple_refl.
Qed.

Lemma max_reg_in_parcode_aux :
  forall elems init pparcb (pc:positive) parcb,
  In pparcb elems ->
  pparcb = (pc, parcb) ->
  Ple (get_max_reg_in_parcb parcb)
    (fold_left
      (fun m p =>
        Pos.max m (get_max_reg_in_parcb (snd p)))
    elems init).
Proof.
  induction elems; intros.
  + inv H.
  + simpl in *.
    destruct H.
    - rewrite H in *.
      simpl in *.
      apply ple_foldmaxparcb_init.
      destruct pparcb. simpl.
      assert (p0 = parcb) by congruence.
      rewrite H1 in *.
      apply Pos.le_max_r.
    - eauto.
Qed.

Lemma max_reg_in_parcode :
  forall parcode pc p,
  parcode ! pc = Some p ->
  Ple (get_max_reg_in_parcb p)
    (get_max_reg_in_parcode parcode).
Proof.
  intros.
  unfold get_max_reg_in_parcode.
  rewrite PTree.fold1_spec.
  eapply max_reg_in_parcode_aux; eauto.
  apply PTree.elements_correct; eauto.
Qed.

Lemma ple_foldmaxreg_init :
  forall l m n,
  Ple m n ->
  Ple
    m
    (List.fold_left (fun (m0 : positive) (parc : parcopy) =>
         Pos.max m0 (get_max_reg_in_parc parc))
      l n).
Proof.
  induction l; intros.
  simpl. auto.
  simpl.
  destruct a. simpl.
  eapply Ple_trans with
    (Pos.max m (CSSAgen.max_reg_in_list (r :: r0 :: nil))); auto.
  apply Pos.le_max_l.
  apply IHl.
  apply Pos.max_le_compat.
  auto. apply Ple_refl.
Qed.

Lemma get_max_reg_in_parcb_correct_src_aux :
  forall l (r : reg) m d,
  In (r,d) (parcb_to_moves l) ->
  Ple r
    (List.fold_left (fun m parc => Pos.max m (get_max_reg_in_parc parc)) l m).
Proof.
  induction l; intros.
  inv H.
  simpl in *.
  flatten H; subst. destruct H.
  + inv H. 
    simpl. eapply ple_foldmaxreg_init; eauto. 
    unfold CSSAgen.max_reg_in_list. simpl.
    eapply Pos.le_trans. 
    2: {
    eapply Pos.le_trans. 
    eapply Pos.le_max_l. 
    eapply Pos.le_max_r.
    }
    eapply Pos.le_max_r.     
  + eapply IHl; eauto.
Qed.

Lemma get_max_reg_in_parcb_dst_correct_aux :
  forall l (r : reg) m d,
  In (r,d) (parcb_to_moves l) ->
  Ple d
    (List.fold_left (fun m parc => Pos.max m (get_max_reg_in_parc parc)) l m).
Proof.
  induction l; intros.
  inv H.
  simpl in *.
  flatten H; subst. destruct H.
  + inv H. 
    simpl. eapply ple_foldmaxreg_init; eauto. 
    unfold CSSAgen.max_reg_in_list. simpl.
    eapply Pos.le_trans. 
    eapply Pos.le_max_r.     
    eapply Pos.le_max_r.     
  + eapply IHl; eauto.
Qed.

Lemma get_max_reg_in_parcb_src_correct :
  forall l r d,
  In (r,d) (parcb_to_moves l) ->
  Ple r (get_max_reg_in_parcb l).
Proof.
  unfold get_max_reg_in_parcb. 
  intros.
  eapply get_max_reg_in_parcb_correct_src_aux; eauto.
Qed.

Lemma get_max_reg_in_parcb_dst_correct :
  forall l r d,
  In (r,d) (parcb_to_moves l) ->
  Ple d (get_max_reg_in_parcb l).
Proof.
  unfold get_max_reg_in_parcb. 
  intros.
  eapply get_max_reg_in_parcb_dst_correct_aux; eauto.
Qed.

Lemma get_maxreg_is_not_temp_parcopies : 
  forall f pc parcb, 
    (fn_parcopycode f) ! pc = Some parcb ->
    Parmov.move_no_temp reg (fun _ => fresh_init f) (parcb_to_moves parcb).
Proof.
  unfold fresh_init, Parmov.move_no_temp, Parmov.is_not_temp.
  intros f pc parcb Hsome ; (intros s d Hin; split; intros _);
  (intro Hcont ; first [ inv Hcont | subst ] ;
   assert (Hple:= max_reg_correct_parccode f);
   rewrite <- Pos.lt_succ_r in Hple;
   eapply max_reg_in_parcode in Hsome; eauto; simpl in *; try invh or; 
   (exploit Pos.le_lt_trans; eauto; intros Hlt;
    eapply Pos.lt_nle  in Hlt;
    elim Hlt;
    replace (Pos.succ (get_maxreg f)) with 
    (fst ((Pos.succ (get_maxreg f)),1)%positive) by go;
    try solve 
        [ eapply get_max_reg_in_parcb_src_correct; eauto
        | eapply get_max_reg_in_parcb_dst_correct; eauto])).
Qed.  

Ltac sz := unfold Plt, Ple in * ; (zify; lia).
Ltac allinv := 
  repeat 
    match goal with 
      | [ H1:   (st_code ?s) ! ?pc = Some _  ,
        H2: (st_code ?s) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1:   Some _ = (st_code ?s) ! ?pc  ,
        H2: (st_code ?s) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | _ => idtac
    end.

(** * Reasoning about monadic computations *)

Remark bind_inversion:
  forall (A B: Type) (f: mon A) (g: A -> mon B) 
         (y: B) (s1 s3: state) (i: state_incr s1 s3),
  bind f g s1 = OK y s3 i ->
  exists x, exists s2, exists i1, exists i2,
  f s1 = OK x s2 i1 /\ g x s2 = OK y s3 i2.
Proof.
  intros until i. unfold bind. destruct (f s1); intros.
  discriminate.
  exists a; exists s'; exists s.
  destruct (g a s'); inv H.
  exists s0; auto.
Qed.

Ltac monadInv1 H :=
  match type of H with
  | (OK _ _ _ = OK _ _ _) =>
      inversion H; clear H; try subst
  | (Error _ _ = OK _ _ _) =>
      discriminate
  | (ret _ _ = OK _ _ _) =>
      inversion H; clear H; try subst
  | (error _ _ = OK _ _ _) =>
      discriminate
  | (bind ?F ?G ?S = OK ?X ?S' ?I) =>
      let x := fresh "x" in (
      let s := fresh "s" in (
      let i1 := fresh "INCR" in (
      let i2 := fresh "INCR" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion _ _ F G X S S' I H) as [x [s [i1 [i2 [EQ1 EQ2]]]]];
      clear H;
      try (monadInv1 EQ2)))))))
  end.

Ltac monadInv H :=
  match type of H with
  | (ret _ _ = OK _ _ _) => monadInv1 H
  | (error _ _ = OK _ _ _) => monadInv1 H
  | (bind ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (bind2 ?F ?G ?S = OK ?X ?S' ?I) => monadInv1 H
  | (?F _ _ _ _ _ _ _ _ = OK _ _ _) => 
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  | (?F _ _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); try monadInv1 H
  | (?F _ = OK _ _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv1 H
  end.

Lemma mfold_unit_step: forall (A: Type) (f: A -> mon unit) l u a s1 s2 INCR,
  mfold_unit f (a::l) s1 = OK u s2 INCR ->
  exists u'' , exists s'', exists INCR'', exists INCR''',
    f a s1 = OK u'' s'' INCR'' 
    /\ (mfold_unit f l s'' = OK u s2 INCR''').
Proof.
  induction l ; intros; monadInv H ; simpl. 
  exists x ; exists s2 ; exists INCR0 ; exists (state_incr_refl s2); auto.
  unfold bind.  exists x ; exists s ; exists INCR0; exists (state_incr_trans s s0 s2 INCR2 INCR3).
  split ; auto. rewrite EQ1; rewrite EQ2; auto. 
Qed.

(** Monotonicity properties of the state *)
Global Hint Resolve state_incr_refl: dessa.
Global Hint Resolve state_incr_trans : dessa.

(** The following tactic saturates the hypotheses with
  [state_incr] properties that follow by transitivity from
  the known hypotheses. *)
Ltac saturateTrans :=
  match goal with
  | H1: state_incr ?x ?y, H2: state_incr ?y ?z |- _ =>
      match goal with
      | H: state_incr x z |- _  =>
         fail 1
      | _ =>
         let i := fresh "INCR" in
         (generalize (state_incr_trans x y z H1 H2); intro i;
          saturateTrans)
      end
  | _ => idtac
  end.

Ltac expl_incr pc := 
  match goal with 
    | [ H : forall pc : positive,
       (st_code ?s0) ! pc = None \/ (st_code ?s0) ! pc = (st_code ?s2) ! pc |- _ ] =>
    eelim (H pc) ; eauto ; (intros ; congruence)
  end.

(** * The implementation of DeSSA satisfies its specification *)


(** ** Properties of auxiliary functions *)
Lemma copy_ins_at:
  forall s1 s2 incr pc max i code u,
  copy_ins pc max i code s1 = OK u s2 incr -> 
  (s2.(st_code)! pc = Some i
    /\ (forall pc', pc' <> pc -> s2.(st_code)!pc' = s1.(st_code)!pc')
    /\ s1.(st_code) ! pc = None).
Proof.
  intros.
  unfold copy_ins in H. 
  flatten H; simpl in *.
  repeat split.
  - rewrite PTree.gss ; auto.
  - intros. rewrite PTree.gso ; auto.
  - destruct (st_wf s1 (st_nextnode_cp s1)).
    + apply Plt_ne in H ; auto. congruence.
    + intuition.
      generalize (st_wf_next_fs s1) (st_wf_next s1) ; intros.
      unfold Plt, Ple, Pos.succ in *. zify ; lia. 
Qed.

Lemma copy_ins_at_renum:
  forall s1 s2 incr pc max i code u,
  copy_ins pc max i code s1 = OK u s2 incr -> 
  (map_pc (st_renum s2)) pc = pc
  /\ 
  (forall pc', pc' <> pc -> 
               (map_pc (st_renum s2)) pc' = (map_pc (st_renum s1)) pc').
Proof.
  intros. 
  unfold copy_ins in H. 
  flatten H; simpl in *.
  unfold map_pc; repeat split.
  - rewrite PTree.gss; auto. 
  - intros. rewrite PTree.gso ; auto.
Qed.

Global Hint Resolve copy_ins_at: dessa.

Lemma reach_moves_incr : forall lnew s1 s2 succ' lastnew block ,
  reach_moves (st_code s1) succ' lastnew block lnew ->
  state_incr s1 s2 ->
  reach_moves (st_code s2) succ' lastnew block lnew.
Proof.
  induction 1 ; intros.
  - econstructor ; eauto.
    inv H0. expl_incr from.
  - exploit IHreach_moves ; eauto. intros HH.
    econstructor 2 with (succ:= succ) ; eauto.  
    inversion H1 ; simpl in *.
    expl_incr from.
Qed.

Lemma copy_ins_next_fs : forall s1 s x pc max ins code INCR,
  copy_ins pc max ins code s1 = OK x s INCR ->
  (st_nextnode_fs s1) = (st_nextnode_fs s).
Proof.
  intros.
  unfold copy_ins in H.
  flatten H; auto.
Qed.

Lemma add_reach_moves : forall opc pc parcb s1 s2 incr,
  add_moves opc pc parcb s1 = OK tt s2 incr ->
  exists lnew, 
    reach_moves (st_code s2) (st_nextnode_fs s1) pc parcb lnew.
Proof.
  unfold add_moves.
  induction parcb ; intros.
  - unfold error in * ; inv H. 
    simpl. exists ((st_nextnode_fs s1)::nil).
    econstructor 1 ; eauto.
    rewrite PTree.gss; auto.
  - destruct a as [src dst]. 
    monadInv H. 
    exploit IHparcb ; eauto. intros [lnew Hlnew].
    exists ((st_nextnode_fs s1)::lnew).  
    econstructor 2 ; eauto.
    clear EQ0 IHparcb.
    unfold add_move in *.
    flatten EQ ; unfold error in * ; simpl in *; try congruence.
    inv INCR0; simpl in *.
    eelim (H2 (st_nextnode_fs s1)); eauto; rewrite PTree.gss; congruence.
Qed.

Lemma add_moves_renum : forall opc pc parcb s1 s2 incr,
  add_moves opc pc parcb s1 = OK tt s2 incr ->
  (match opc with 
     | Some opc => (forall pc', pc' <> opc -> (st_renum s2) ! pc' = (st_renum s1) ! pc')
                   /\ (st_code s2) ! (map_pc (st_renum s2) opc) = Some (RTL.Inop pc)
     | None => (forall pc, (st_renum s2) ! pc = (st_renum s1) ! pc)               
   end).
Proof.
  unfold add_moves.
  induction parcb ; intros.
  - unfold error in * ; inv H. 
    simpl in *. flatten. 
    split. 
    + intros. rewrite PTree.gso; auto.
    + unfold map_pc. 
      rewrite PTree.gss. 
      rewrite PTree.gss ; auto.
  - destruct a as [src dst]. 
    monadInv H.
    assert (HH:= IHparcb _ _ _ EQ0). 
    unfold add_move in *.
    flatten EQ ; unfold error in * ; simpl in *; try congruence.
Qed.

Lemma add_moves_renum_last : forall opc parcb pc s1 s2 incr,
                               pc <> opc ->
  add_moves (Some opc) pc parcb s1 = OK tt s2 incr ->
  (parcb = nil /\ map_pc (st_renum s2) pc = (map_pc (st_renum s1) pc))
  \/  exists lnew, 
        reach_moves (st_code s2) (st_nextnode_fs s1) pc parcb lnew /\
        exists rpc (lnew' : list node),
          rev lnew = rpc :: lnew' /\ 
          (map_pc (st_renum s2) opc) = rpc.
Proof.
  intros. 
  exploit add_moves_renum; eauto. simpl. intros [Hunch Hcode].
  induction parcb.
  - inv H0; simpl in *.
    left; split; eauto.
    unfold map_pc; erewrite Hunch; eauto.
  - right. 
    exploit add_reach_moves; eauto. intros [lnew Hreach].
    monadInv H0.
    exploit IHparcb; eauto. 
    + intros. 
      unfold add_move in *. 
      flatten EQ; simpl in *; eauto. 
    + clear IHparcb. 
      intros; invh or ; try invh and.
      simpl in *.
      * invh reach_moves.
        invh reach_moves.
        exists (((st_nextnode_fs s1)::succ::nil)).
        { split.
          - econstructor; go.
          - simpl. 
            exists succ; exists ((st_nextnode_fs s1)::nil).
            split; go. 
            monadInv EQ0; flatten EQ0; simpl in *; go.
            flatten EQ; subst; simpl in *.
            rewrite PTree.gso in H5; try (zify ; lia).
            rewrite PTree.gss in H5. 
            unfold map_pc. rewrite PTree.gss.
            congruence.
        }
      * destruct H1 as [lnew' [Hreach' [rpc [lnew'' [Hrev Hmap]]]]].
        destruct a as [src dst]. 
        exists ((st_nextnode_fs s1)::lnew'). 
        { split. 
          - econstructor; go.
            inversion INCR0; subst.
            monadInv EQ; flatten EQ; simpl in *. 
            eelim (H3 (st_nextnode_fs s1)); eauto; rewrite PTree.gss; auto; try congruence.
          - simpl. rewrite Hrev. simpl. 
            go.
        }
Qed.

Ltac kick := 
  match goal with 
    | [ H: (RTLpar.fn_code ?f) ! _ = Some (Itailcall _ (inl ident _) _) |- _] =>
      econstructor 8 ; eauto
    | [ H: (RTLpar.fn_code ?f) ! _ = Some (Icall _ (inl ident _) _ _ _) |- _] =>
      econstructor 6 ; eauto
    | _ =>      
      (econstructor ; eauto)
  end ; 
  (intros rr Hrr; try inv Hrr).

(** ** Correctness of [copy_wwo_add] *)
Lemma copy_wwo_add_dssa_spec: forall f (WF: wf_function f) fresh pc max s1 s2 incr ins, 
  (fn_code f) ! pc = Some ins ->
  copy_wwo_add fresh (make_predecessors (fn_code f) SSA.successors_instr) 
               (fn_code f) (fn_parcopycode f) max pc s1 = OK tt s2 incr ->
  rtldpar_spec fresh (fn_code f) (fn_parcopycode f) (st_code s2) (map_pc (st_renum s2))
               pc.
Proof.
  intros.
  unfold copy_wwo_add in H0.
  rewrite H in *.
  destruct ins;  
    (try match goal with 
       | [H: (RTLpar.fn_code ?f) ! ?pc = Some ?ins  |- _ ] => 
         case_eq (map_pamr size ins) ; intros i Hi ; rewrite Hi in * ; 
           generalize Hi ; inv Hi ; intros Hi ; try congruence
     end;
    try match goal with 
      | [H : (if ?t_if then _ else _) = _ |- _ ] => 
        case_eq t_if ; intros Hif ; rewrite Hif in * ; boolInv ; try congruence
    end;
    try  match goal with 
           | [ros: (reg + ident)%type |- _ ] => 
             case_eq (ros_pamr size ros) ; intros ros' Hros ; rewrite Hros in *;
               [(destruct ros ; [ (exploit ros_pamr_true ; eauto) ; intros Hvalid |])|] ; 
               try congruence
           | _ => idtac  
         end;
    try solve [((econstructor 4 ; eauto ; try kick ; try congruence);
                [(exploit copy_ins_at ; eauto ; (intros ; intuition ; (inv H2 ; eauto) ))
                | exploit copy_ins_at_renum ; eauto; intros [Hmap Hunch]; unfold map_pc in *; rewrite Hmap at 1; auto])]).

  - (* Nop *)
    flatten H0; subst. 
    + monadInv H0.
      unfold copy_inop in EQ. 
      exploit copy_ins_at; eauto; intros; repeat invh and. 
      exploit copy_ins_next_fs; eauto; intros Heq.
      inversion INCR1; subst.
      
      eelim (H6 pc) ; eauto; try congruence.
      intros Hpc. rewrite Hpc in H1. rewrite Heq in *.
      destruct x0. 
      assert (n <> pc). 
        { intro; subst. 
          eelim fn_parcb_jp ; eauto. 
          - intros. unfold successors_list in Eq. 
            rewrite Hpreds in Eq. inv Eq; go.
          - intro Hcont.
            invh join_point.
            unfold successors_list in Eq. 
            rewrite Hpreds in Eq. inv Eq; go.
        }
      exploit add_moves_renum_last; eauto. 
      assert (JP: is_jp pc (fn_code f)).
      { exploit RTLpar.fn_parcb_jp ; eauto.
        - intro Hcont.
          invh join_point.
          unfold successors_list in Eq. 
          rewrite Hpreds in Eq. inv Eq; go.
        - intros. invh join_point ; go.
      }
      intros [Case1 | Case2].
      * invh and.
        exploit add_reach_moves; eauto. intros [lnew Hlnew].
        exploit reach_moves_last_inop; eauto. intros.
        rewrite H8 in *.
        generalize Hlnew ; invh reach_moves. intros Hlnew.
        simpl in H10.
        repeat invh ex ; invh and. inv H12.
        
        { econstructor 3 with (lnew:= nil) ; eauto ; go.
          - rewrite H8 in *. simpl.
            simpl in EQ1; monadInv EQ1; unfold map_pc; simpl. 
            rewrite PTree.gss; auto.            
          - exploit add_moves_renum ; eauto. intros [Hmapoth Hmapn]. auto.
        }        
      * { repeat (repeat invh ex ; repeat invh and).
          assert (x0 = rev (map_pc (st_renum s2) pc :: x2)).
          { rewrite <- H8; rewrite rev_involutive; eauto. }
          subst. simpl in H9.
          econstructor 3 ; go.
          - exploit add_moves_renum ; eauto. intros [Hmapoth Hmapn]. auto.
        }      
    + econstructor 1; eauto.
      * intro Hcont. invh is_jp.
        unfold successors_list in *; flatten Eq. subst. go. 
      * eapply copy_ins_at; eauto.
      * exploit copy_ins_at_renum; eauto ; intros ; invh and; auto.
      
    + monadInv H0. 
      unfold copy_inop in EQ. 
      exploit copy_ins_at; eauto; intros; repeat invh and. 
      exploit copy_ins_next_fs; eauto; intros Heq.
      inversion INCR1; subst.
      
      eelim (H6 pc) ; eauto; try congruence.
      intros Hpc. rewrite Hpc in H1. rewrite Heq in *.
      destruct x0. 
      exploit add_reach_moves; eauto. intros [lnew Hreach].
      econstructor 2; go.
      * intro Hcont. invh is_jp. 
        eelim (fn_normalized_jp f WF pc n); eauto; go. 
        unfold successors_list in *; flatten Eq ; go.
      * exploit add_moves_renum; eauto. simpl. 
        intros.
        unfold map_pc. erewrite H7; eauto.
        exploit copy_ins_at_renum; eauto; intros ; invh and; auto.
Qed.

Lemma copy_ins_unch_renum : forall  pc max ins code s1 s2 INCR,
   copy_ins pc max ins code s1 = OK tt s2 INCR ->
   forall pc', pc' <> pc -> (map_pc (st_renum s2)) pc' = (map_pc (st_renum s1) pc'). 
Proof.
  unfold copy_ins; intros.
  flatten H; simpl.
  unfold map_pc.
  rewrite PTree.gso; auto.
Qed.

Lemma copy_wwo_unch_renum : forall preds code pcode fresh max s1 s2 incr pc, 
  (copy_wwo_add fresh preds code pcode max) pc s1 = OK tt s2 incr ->
  forall pc', pc <> pc' -> (map_pc (st_renum s2)) pc' = (map_pc (st_renum s1) pc'). 
Proof.
  intros.
  unfold copy_wwo_add in *. 
  flatten H; subst; auto; 
  try solve [eapply copy_ins_at_renum; eauto].
  - monadInv H. destruct x, x0.
    exploit  add_moves_renum; eauto; intros. 
    exploit copy_ins_unch_renum; eauto. intros. 
    simpl in *; invh and.
    unfold map_pc. erewrite H2; eauto. 
  - monadInv H. destruct x, x0.
    exploit  add_moves_renum; eauto; intros. 
    exploit copy_ins_unch_renum; eauto. intros. 
    simpl in *.
    unfold map_pc. rewrite H; eauto. 
  - monadInv H. destruct x, x0.
    exploit  add_moves_renum; eauto; intros. 
    exploit copy_ins_unch_renum; eauto. intros. 
    simpl in *. invh and.
    unfold map_pc. rewrite H2; eauto. 
  - monadInv H. destruct x, x0.
    exploit  add_moves_renum; eauto; intros. 
    exploit copy_ins_unch_renum; eauto. intros. 
    simpl in *. 
    unfold map_pc. rewrite H; eauto. 
Qed.

Lemma mfold_copy_wwo_unch_renum : forall preds code pcode fresh l max s1 s2 incr, 
  mfold_unit (copy_wwo_add fresh preds code pcode max) l s1 = OK tt s2 incr ->
  forall pc, ~ In pc l -> (map_pc (st_renum s2)) pc = (map_pc (st_renum s1) pc). 
Proof.
  induction l ; intros.
  - monadInv H ; go. 
  - exploit mfold_unit_step ; eauto.
    intros [u' [s0 [INCR0 [INCR1 [Haddnop Hmfold]]]]].
    destruct u'.
    exploit IHl; eauto. 
    intros Heq; rewrite Heq.
    eapply copy_wwo_unch_renum; go.
Qed.
    
Lemma mfold_dssa_spec : forall f (WF: wf_function f) fresh l max s1 s2 incr, 
  mfold_unit 
    (copy_wwo_add fresh 
                  (make_predecessors (fn_code f) successors_instr)
                  (fn_code f) (RTLpar.fn_parcopycode f) max)
    l s1 = OK tt s2 incr ->
  (list_norepet l) ->
  forall pc ins, 
    In pc l -> (fn_code f) ! pc = Some ins ->
    rtldpar_spec fresh (fn_code f) (fn_parcopycode f) 
                 (st_code s2) (map_pc (st_renum s2)) pc. 
Proof.
  induction l ; intros; go.
  invh In. 
  - exploit mfold_unit_step ; eauto.
    intros [u' [s0 [INCR0 [INCR1 [Haddnop Hmfold]]]]].
    destruct u'.
    exploit copy_wwo_add_dssa_spec ; eauto. intros.
    inversion INCR1. 
    invh rtldpar_spec.  
    + econstructor ; eauto.
      expl_incr pc. 
      invh list_norepet.
      erewrite mfold_copy_wwo_unch_renum; eauto.
    + econstructor 2 with (succ:= succ) (fresh:= fresh0)  (lnew:= lnew); eauto.
      expl_incr pc. 
      eapply reach_moves_incr;  eauto.
      invh list_norepet.
      erewrite mfold_copy_wwo_unch_renum; eauto.
    + econstructor 3 with (succ:= succ) (fresh:= fresh0)  (lnew:= lnew); eauto. 
      expl_incr pc. 
      eapply reach_moves_incr;  eauto.
      * invh list_norepet;
        erewrite mfold_copy_wwo_unch_renum; eauto.
      * assert (Hmappc: (map_pc (st_renum s2) pc) = (map_pc (st_renum s0) pc)) 
        by ( invh list_norepet;
             erewrite mfold_copy_wwo_unch_renum; eauto).
        rewrite Hmappc.
        eelim (H6 (map_pc (st_renum s0) pc)) ; eauto; try congruence. 
    + econstructor 4; eauto.
      expl_incr pc. 
      invh list_norepet.
      erewrite mfold_copy_wwo_unch_renum; eauto.
  - exploit mfold_unit_step ; eauto.
    intros [u' [s0 [INCR0 [INCR1 [Haddnop Hmfold]]]]].
    destruct u'.      
    exploit IHl ; eauto. inv H0 ; auto.
Qed.  

Lemma NoDup_list_norepet : forall (A: Type) (l:list A), NoDup l -> list_norepet l.
Proof.
  induction 1; go. 
Qed.  

Lemma list_norepet_NoDup : forall (A: Type) (l:list A), list_norepet l -> NoDup l.
Proof.
  induction 1; go. 
Qed.

Lemma get_max_fold''' : forall l maxacc lacc,
  NoDup (l++lacc) ->
  NoDup (snd (fold_left (fun (al: positive * list positive) pc => let (a,l) := al in if plt a pc then (pc,pc::l) else (a,pc::l)) l (maxacc,lacc))).
Proof.
  induction l ; intros ; inv H.
  simpl in H0. inv H0. simpl. constructor.
  simpl in *. inv H2. econstructor ; eauto. 
  simpl in *.
  destruct (plt maxacc a); eapply IHl ; eauto;
    ((eapply NoDup_list_norepet in H3);
      (eapply Coqlib.list_norepet_app in H3; intuition);
      (eapply list_norepet_NoDup ; eauto);
      (eapply Coqlib.list_norepet_app; intuition ; auto);
      [ (constructor ; auto; (intro Hcont ; elim H2; eapply in_app ; eauto))
        | (unfold list_disjoint; intros; intro Hcont; first [ inv Hcont | subst] ;
           inv H4 ;  [ (elim H2; eapply in_app ; eauto) | exploit H3 ; eauto])]).
Qed.

Lemma get_max_nodup : forall (A: Type) t, 
  NoDup (snd (@get_max A t)).
Proof.
  unfold get_max.
  intros. eapply get_max_fold''' ; eauto.
  rewrite <- app_nil_end.
  apply list_norepet_NoDup.
  apply PTree.elements_keys_norepet.
Qed.

Definition mapping (f: function) : (PTree.t node) :=
  let '(init,max,lp) := init_state f in 
  let fresh := fresh_init f in
  let preds := make_predecessors (fn_code f) SSA.successors_instr in
  match mfold_unit (copy_wwo_add fresh  
                                 preds (fn_code f) (fn_parcopycode f) max)
                   (sort_pp lp) init with
    | Error m => PTree.empty node
    | OK u s'' H => (st_renum s'')
  end.
  
(** ** Specification compliancy of the implementation *)
Lemma transl_function_spec_ok : forall f (WF: wf_function f) tf, 
    transl_function f = Errors.OK tf -> 
    transl_function_spec f tf (map_pc (mapping f)).
Proof.
  unfold transl_function, mapping.
  intros ; flatten H ; boolInv.
  destruct u. 
  econstructor; eauto.
  simpl. 
  unfold sort_pp in *.
  generalize (PosSort.Permuted_sort l)  ; intros.
  assert (l = snd (get_max (fn_code f)))
    by (unfold init_state in *; congruence); subst.
  exploit mfold_dssa_spec ; eauto.
  + eapply NoDup_list_norepet ; auto.
    eapply Permutation_NoDup ; eauto.
    apply get_max_nodup.
  + exploit get_max_in ; eauto.
    eapply Permutation_in ; eauto.
Qed.

(** * Semantic preservation *)
(** We show here that the specification of RTLdpar is correct *)

Require Import Linking.

Section PRESERVATION.

  Definition match_prog (p: RTLpar.program) (tp: RTL.program) :=
    match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

  Lemma transf_program_match:
    forall p tp, transl_program p = Errors.OK tp -> match_prog p tp.
  Proof.
    intros. apply match_transform_partial_program; auto.
  Qed.

  Section CORRECTNESS.

    Variable prog: RTLpar.program.
    Variable tprog: RTL.program.
    Hypothesis TRANSF_PROG: match_prog prog tprog.
    Hypothesis WF_PROG : wf_program prog.
    Hypothesis MILL_PROG : mill_program prog.

    Let ge := Genv.globalenv prog.
    Let tge := Genv.globalenv tprog.

    Let sem := RTLpar.semantics prog.
    Let tsem := RTL.semantics tprog.

    Lemma symbols_preserved:
      forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
    Proof.
      eapply Genv.find_symbol_transf_partial ; eauto. 
    Qed.

    Lemma functions_translated:
      forall (v: val) (f: fundef),
        Genv.find_funct ge v = Some f ->
        exists tf, Genv.find_funct tge v = Some tf 
                   /\ transl_fundef f = Errors.OK tf.
    Proof.
      eapply Genv.find_funct_transf_partial; eauto.
    Qed.

    Lemma function_ptr_translated:
      forall b (f: fundef),
        Genv.find_funct_ptr ge b = Some f ->
        exists tf, Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = Errors.OK tf.
    Proof.
      eapply Genv.find_funct_ptr_transf_partial; eauto.
    Qed.

    Lemma sig_fundef_translated:
      forall f tf,
        transl_fundef f = Errors.OK tf ->
        RTL.funsig tf = funsig f.
    Proof.
      intros f tf. intros.
      case_eq f ; intros; subst. 
      - Errors.monadInv H.
        simpl.
        unfold transl_function in *. flatten EQ; auto. 
      - inv H. auto.
    Qed.

    Lemma sig_function_translated:
      forall f tf,
        transl_function f = Errors.OK tf ->
        RTL.fn_sig tf = fn_sig f.
    Proof.
      intros f tf. destruct f; simpl; intros.
      unfold transl_function in * ; flatten H ; auto.  
    Qed. 

    Lemma spec_ros_r_find_function:
      forall  rs rs' f r m,
        find_function ge (RTLpar.ros_to_vos m (inl _ r) rs) rs = Some f ->
        rs# r = rs'#r ->
        exists tf,
          RTL.find_function tge (RTL.ros_to_vos m (inl _ r) rs') rs' = Some tf
          /\ RTLdpar.transl_fundef f = Errors.OK tf.
    Proof.
      intros. ss. des_ifs.
      eapply functions_translated; eauto.
      eapply functions_translated; eauto.
    Qed.

    Lemma spec_ros_id_find_function:
      forall rs rs' f id m,
        find_function ge (RTLpar.ros_to_vos m (inr _ id) rs) rs = Some f ->
        exists tf,
          RTL.find_function tge (RTL.ros_to_vos m (inr _ id) rs') rs' = Some tf
          /\ RTLdpar.transl_fundef f = Errors.OK tf.
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
        fn_stacksize f = RTL.fn_stacksize tf.
    Proof.
      unfold transl_function; intros; flatten H ; auto.
    Qed.

    Lemma senv_preserved:
      Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
    Proof.
      eapply Genv.senv_transf_partial; eauto.
    Qed.
    
    Lemma same_public:
      prog_public prog = prog_public tprog.
    Proof. inv TRANSF_PROG. des; eauto. Qed.

Create HintDb valagree.
Hint Resolve symbols_preserved : valagree.
Hint Resolve eval_addressing_preserved : valagree.
Hint Resolve eval_operation_preserved : valagree.
Hint Resolve sig_function_translated : valagree.
Hint Resolve sig_fundef_translated : valagree.
Hint Resolve senv_preserved : valagree.
Hint Resolve stacksize_preserved: valagree.


Definition parcopy_store_e (parcb: list (reg * reg) ) (rs: regset) : regset :=
  fold_left (fun rs parc => 
               match parc with 
                 | (src,dst) => rs# dst <- (rs# src)
               end) parcb rs.
    
Lemma reach_moves_star :  forall mvs fresh ts sp rs  m tf  succ lnew ,
  reach_moves (RTL.fn_code tf) fresh succ mvs lnew ->
  DStar tsem (RTL.State ts tf sp fresh rs m) E0 
                    (RTL.State ts tf sp succ (parcopy_store_e mvs rs) m).
Proof.
  induction mvs; intros.
  - simpl in *.  
    invh reach_moves.
    eapply star_step ; try DStep_tac ; eauto; go.
  - invh reach_moves. 
    eapply star_step 
    with  (s2 := (RTL.State ts tf sp succ0 
                            rs # dst <- 
                            (rs# src)) m) (t2:= E0) (t1:= E0); auto; try DStep_tac.
    + eapply RTL.exec_Iop ; eauto. 
    + exploit IHmvs; eauto.
Qed.

Lemma rev_nil_nil {A: Type} : forall (l:list A), rev l = nil -> l = nil.
Proof.
 intros.
 change nil with (@rev A nil) in H.
 rewrite <- rev_involutive.
 rewrite <- rev_involutive at 1.
 congruence.
Qed.

Lemma reach_moves_star_last :  forall mvs l fresh tf succ,
  reach_moves (RTL.fn_code tf) fresh succ mvs l ->
  forall a lnew, rev l = (a::lnew) ->
  forall  ts sp rs  m,               
  DStar tsem (RTL.State ts tf sp fresh rs m) E0 
                    (RTL.State ts tf sp a (parcopy_store_e mvs rs) m).
Proof.
  induction 1 ; intros. 
  - simpl in *. inv H0.
    eapply star_refl ; eauto. 
  - simpl in *. eapply star_step ; try DStep_tac; eauto.
    + eapply RTL.exec_Iop ; eauto; go.
    + case_eq (rev l) ; intros. 
      * exploit @rev_nil_nil; eauto ; intros. 
        subst. invh reach_moves.
      * rewrite H2 in * ; inv H1.        
        eapply IHreach_moves; eauto; go.
    + auto.
Qed.

(** ** Simulation relation *)
Variant match_regset (f: function) : SSA.regset -> RTL.regset -> Prop := 
| mrg_intro : forall rs rs', 
  (forall r, 
    no_fresh f r ->
    rs# r = rs'# r) ->
    match_regset f rs rs'.

Lemma match_regset_args : forall f args rs rs' , 
  match_regset f rs rs' ->
  (forall arg, In arg args -> no_fresh f arg) ->
  rs## args = rs'##  args.
Proof.
  induction args ; intros.
  - simpl ; auto.
  - simpl.
    erewrite IHargs; eauto. 
    inv H. erewrite H1; eauto.
Qed.
Hint Resolve match_regset_args : valagree.  

Inductive match_stackframes : list stackframe -> list RTL.stackframe -> Prop :=
| match_stackframes_nil: match_stackframes nil nil
| match_stackframes_cons: 
  forall res f sp pc rs rs' s tf ts
    (STACK : match_stackframes s ts)
    (SPEC: transl_function f = Errors.OK tf)
    (WF: wf_function f)
    (MILL: mill_function f)
    (MREG: match_regset f rs rs'),
    match_stackframes
    ((Stackframe res f sp pc rs) :: s)
    ((RTL.Stackframe res tf sp (map_pc (mapping f) pc) rs') :: ts).
Hint Constructors match_stackframes: core.

Set Implicit Arguments.

Variant match_states: RTLpar.state -> RTL.state -> Prop :=
  | match_states_intro:
    forall s ts sp pc rs rs' m f tf
     (WF: wf_function f)
     (MILL: mill_function f)
     (SPEC: transl_function f = Errors.OK tf)
     (STACK: match_stackframes s ts)
     (MREG: match_regset f rs rs'),
      match_states (State s f sp pc rs m) (RTL.State ts tf sp ((map_pc (mapping f)) pc) rs' m)
  | match_states_call:
    forall s ts f tf args m 
     (WF: wf_fundef f)
     (MILL: mill_fundef f)
     (SPEC: transl_fundef f = Errors.OK tf)
     (STACK: match_stackframes s ts),
      match_states (Callstate s f args m) (RTL.Callstate ts tf args m)
  | match_states_return:
      forall s ts v m 
     (STACK: match_stackframes s ts ),
        match_states (Returnstate s v m) (RTL.Returnstate ts v m).
Hint Constructors match_states: core.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
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
    + eapply Genv.find_funct_ptr_prop ; eauto.   
    + eapply Genv.find_funct_ptr_prop ; eauto.  
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> RTL.final_state st2 r.
Proof.
  intros; invh match_states; invh final_state. 
  invh match_stackframes; go.
Qed.

Ltac normalized pc :=
  match goal with
    | [NORM : forall (pc: positive) (ins: SSA.instruction), _ -> 
          rtldpar_spec ?tmp ?code1 ?pcode1 ?code2 ?R pc |- _] =>
      let Hpc := fresh "Hpc" in
        let Hnorm := fresh "Hnorm" in
        assert (Hpc := NORM pc); 
          exploit Hpc ; eauto ; clear Hpc ; intro Hnorm ; inv Hnorm ; allinv ; try congruence
  end;
  try invh map_pamr;
  try match goal with 
        | [H: (if ?t_if then _ else _) = _ |- _ ] => destruct t_if ; try congruence ; inv H
      end.

Ltac allinv_par := 
  repeat 
    match goal with 
      | [H: value ?s = Some ?s' |- _ ] => inv H
      | [ H1: (RTL.fn_code ?tf) ! ?pc = Some _  ,
          H2: (RTL.fn_code ?tf) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1: (RTLpar.fn_code ?tf) ! ?pc = Some _  ,
          H2: (RTLpar.fn_code ?tf) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1: (RTLpar.fn_parcopycode ?tf) ! ?pc = Some _  ,
          H2: (RTLpar.fn_parcopycode ?tf) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | _ => idtac
    end.

Lemma exec_seq_parcopy_store_e : forall p rs r,
        (Parmov.exec_seq reg peq val (rev p) (fun r => rs !! r) r =
        (parcopy_store_e (rev p) rs) # r).
Proof.
  clear.
  intros. rewrite <- Parmov.exec_seq_exec_seq_rev.
  induction p ; intros; go.
  unfold parcopy_store_e.
  erewrite <- fold_left_rev_right.
  rewrite rev_involutive.
  simpl Parmov.exec_seq_rev. flatten; subst. 
  destruct (peq r r1).
  - subst. 
    rewrite Parmov.update_s; auto.
    simpl.
    replace p with (rev (rev p)) by eauto using rev_involutive.
    rewrite rev_involutive at 1.
    rewrite PMap.gss.
    erewrite IHp; eauto; go.
    erewrite fold_left_rev_right.
    unfold parcopy_store_e; eauto. 
  - rewrite Parmov.update_o; auto.
    simpl.
    replace p with (rev (rev p)) by eauto using rev_involutive.
    rewrite rev_involutive at 1.
    rewrite PMap.gso; auto.
    erewrite IHp; eauto.
    erewrite fold_left_rev_right.
    unfold parcopy_store_e; eauto.    
Qed.

Lemma exec_par_parcopy_store : forall f p rs rs' r,
                                 match_regset f rs rs' ->
  forall 
    (FRESH : Parmov.move_no_temp reg (fun _ : reg => (fresh_init f))
                                      (parcb_to_moves p))
    (NOFRESH: no_fresh f r),
    (parcopy_store p rs) !! r =
    Parmov.exec_par reg peq val (parcb_to_moves p)
                    (fun r => rs' # r) r.
Proof.
  induction p ; intros; go.
  - simpl. 
    invh match_regset; eauto.
  - destruct a as [src dst].
    simpl. 
    destruct (peq r dst).
    + subst.
      rewrite Parmov.update_s; auto.
      rewrite PMap.gss.
      invh match_regset.
      eapply H0; eauto; go.
      simpl in *. unfold Parmov.move_no_temp in *.
      exploit FRESH; eauto; go; intuition.
    + rewrite PMap.gso; auto.
      rewrite Parmov.update_o; eauto.
      eapply IHp; eauto.
      simpl in *. unfold Parmov.move_no_temp in *; go.      
Qed.
  
Lemma match_regset_parmoves: 
  forall f rs rs' p,
  forall (FRESH : Parmov.move_no_temp reg (fun _ : reg => (fresh_init f)) (parcb_to_moves p))
         (MILL: Parmov.is_mill reg (parcb_to_moves p)),
    match_regset f rs rs' ->
    match_regset f (parcopy_store p rs)
                 (parcopy_store_e (seq_parmoves (fresh_init f) (parcb_to_moves p)) rs').
Proof.
  clear. intros.
  assert (Hcor: forall e,
      Parmov.env_equiv reg (fun _ => fresh_init f) val
                       (Parmov.exec_seq reg peq val (Parmov.parmove reg peq (fun _ => fresh_init f)
                                                                     (parcb_to_moves p)) e) 
                       (Parmov.exec_par reg peq val (parcb_to_moves p) e))
    by (eapply Parmov.parmove_correctness ; eauto). 
  specialize (Hcor (fun r => rs' # r)).
  econstructor; eauto. intros.  
  specialize (Hcor r H0).
  replace (Parmov.parmove reg peq (fun _ : reg => fresh_init f)
        (parcb_to_moves p)) with (rev (rev (Parmov.parmove reg peq (fun _ : reg => fresh_init f)
        (parcb_to_moves p)))) in * by eauto using rev_involutive.
  
  erewrite exec_seq_parcopy_store_e in Hcor ; eauto. 
  rewrite rev_involutive in Hcor.  
  unfold seq_parmoves. rewrite Hcor.
  eapply exec_par_parcopy_store; eauto.
Qed.
  
Lemma wf_njp_id : forall f (WF: wf_function f) tf R pc,
  (transl_function_spec f tf R) ->
  forall ins, (fn_code f) ! pc = Some ins ->
  ~ (join_point pc f) ->
  (R pc = pc). 
Proof.
  induction 1 ; intros.
  invh transl_function_spec.
  exploit DPARSPEC; eauto; intros; invh rtldpar_spec; go.
  elim H1; invh is_jp; go.
Qed.

Lemma wf_ninop_id_succ : forall f (WF: wf_function f) tf R pc,
  (transl_function_spec f tf R) ->
  forall ins, (fn_code f) ! pc = Some ins ->
  (forall s, ins <> Inop s) ->
  forall s, In s (successors_instr ins) ->  (R s = s). 
Proof.
  induction 1 ; intros.
  assert (~ join_point s f).
  { intro Hcont; 
    exploit (fn_normalized s pc); eauto; go.
    unfold successors_list, successors.
    rewrite PTree.gmap1.
    unfold option_map ; rewrite H0; auto.
  }
  exploit fn_code_closed; go. intros [ins' Hins']. 
  eapply wf_njp_id; go. 
Qed.
    
(** ** This relation is indeed a simulation *)
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
    | [  |- context [RTL.Returnstate ?ts ?vres ?m]] => idtac
    | _ => 
      ( (exploit transl_function_spec_ok ; eauto; intros))
  end; 
  try match goal with 
    | [SPEC: transl_function_spec ?f ?tf ?R |- _ ] => 
      generalize SPEC ; inv SPEC ; intros SPEC
  end; allinv_par.
  
  - (* inop without *)
    normalized pc; allinv_par.
    
    + rewrite H7.
      exists (RTL.State ts tf sp succ rs' m). split.
      * eapply plus_one; DStep_tac; eauto.
        econstructor; eauto.
      * clear H7. subst. 
        
        assert (HRsucc: succ = (map_pc (mapping f)) succ). 
        { symmetry. 
          specialize (DPARSPEC succ).
          exploit fn_code_closed; go. intros [ins' Hsucc].
          eapply wf_njp_id with (tf:= tf); eauto using transl_function_spec_ok; go. 
        }
        rewrite HRsucc at 2. 
        econstructor ; eauto.
        
    + subst. elim H3. 
      exploit fn_parcb_jp; eauto. intro Hcont.
      invh join_point; go. 

    + exists (RTL.State ts tf sp succ rs' m). split.
      * eapply plus_one; DStep_tac; eauto.
        econstructor; eauto.
      * assert (HRsucc: succ = (map_pc (mapping f)) succ). 
        { symmetry. 
          specialize (DPARSPEC succ).
          exploit fn_code_closed; go. intros [ins' Hsucc].
          eapply wf_njp_id with (tf:= tf); eauto using transl_function_spec_ok; go. 
        }
        rewrite HRsucc at 2. 
        econstructor ; eauto.

  - (* inop with par blocks *)
    normalized pc; allinv_par.
    + rewrite H11 in *. clear H11. subst.
      assert (Hinssucc: exists s, (fn_code f) ! succ = Some (Inop s))
          by (eapply fn_parcb_inop; eauto; go). 
      destruct Hinssucc as [succ' Hinssucc].
      specialize (DPARSPEC succ); eauto. 
      exploit DPARSPEC; eauto. intros.
      invh rtldpar_spec; repeat invh or ; try congruence; allinv_par.
      * elim H9; eauto. 
        invh join_point; go.
      * exists
        (RTL.State ts tf sp (map_pc (st_renum s0) succ)
                   (parcopy_store_e (seq_parmoves (fresh_init f) (parcb_to_moves parcb))
                   (parcopy_store_e (seq_parmoves (fresh_init f) (parcb_to_moves parcb0))
                                    rs')) m). 
        { split.
          - eapply plus_left; try DStep_tac; eauto. 
            + econstructor; eauto.
            + eapply star_trans; eauto.
              * eapply reach_moves_star in H10; eauto.
              * eapply star_trans; eauto. 
                eapply star_step; try DStep_tac; eauto; go.
                eapply reach_moves_star_last ; eauto using rev_involutive.
            + auto.
          - rewrite H7. econstructor; eauto. 
            eapply match_regset_parmoves; eauto.
            + eapply get_maxreg_is_not_temp_parcopies ; eauto. 
            + eapply match_regset_parmoves; eauto.  
              eapply get_maxreg_is_not_temp_parcopies ; eauto.
        }

    + eelim fn_normalized_jp with (pc':= succ) (pc:= pc); eauto; go.
      invh is_jp ; go.

  - (* iop *) 
    normalized pc; allinv_par.
    rewrite H6 in *. clear H6. subst. 
    exists  (RTL.State ts tf sp pc' (rs' # res <- v) m). 
    split.
    + eapply plus_one ; try DStep_tac; eauto. 
      simpl in *. econstructor 2 ; eauto.
      rewrite <- H0 ; eauto.
      symmetry.
      erewrite match_regset_args ; eauto with valagree.
      symmetry. eapply eval_operation_wrapper_preserved.
      eapply senv_preserved.
      assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
    + assert (HRpc': map_pc (mapping f) pc' = pc') 
        by (eapply wf_ninop_id_succ; eauto using transl_function_spec_ok; go).
      rewrite <- HRpc' at 2. clear HRpc'.
      econstructor 1 ; auto.  
      constructor; intros. 
      destruct (peq res r).
      inv e. rewrite PMap.gss. rewrite PMap.gss; auto.
      rewrite PMap.gso; auto. rewrite PMap.gso ; auto. inv MREG ; auto.
      
      
  - (* iload *)
    normalized pc; allinv_par.
    rewrite H7 in * ; clear H7. subst.
    exists  (RTL.State ts tf sp pc' (rs'#dst <- v) m).
    split.
    + eapply plus_one ; try DStep_tac; eauto. 
      simpl in *. econstructor 3 ; eauto.
      rewrite <- H0 ; eauto.
      symmetry. erewrite match_regset_args ; eauto with valagree. 
      assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
    + assert (HRpc': map_pc (mapping f) pc' = pc') 
        by (eapply wf_ninop_id_succ; eauto using transl_function_spec_ok; go).
      rewrite <- HRpc' at 2. clear HRpc'.
      econstructor 1 ; auto.
      constructor. intros. destruct (peq dst r).
      inv e. rewrite PMap.gss. rewrite PMap.gss; auto.
      rewrite PMap.gso; auto. rewrite PMap.gso; auto. inv MREG ; auto.
      
  - (* istore *)
    normalized pc ; allinv_par.
    rewrite H7 in * ; clear H7 ; subst.
    exists  (RTL.State ts tf sp pc' rs' m'). split.
    + eapply plus_one ; try DStep_tac; eauto. 
      econstructor 4 with (a:= a) ; eauto. 
      * rewrite <- H0 ; eauto with valagree.
        symmetry. erewrite match_regset_args ; eauto with valagree.
        assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
      * inv MREG. erewrite <- H3 ; eauto.
        assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
    + assert (HRpc': map_pc (mapping f) pc' = pc')
        by (eapply wf_ninop_id_succ; eauto using transl_function_spec_ok; go).
      rewrite <- HRpc' at 2. clear HRpc'.      
      econstructor 1 ; auto.

  - (* icall *)
    normalized pc; allinv_par. 
    rewrite H6 in * ; clear H6 ; subst.
    destruct ros.
    + exploit (spec_ros_r_find_function rs rs') ; eauto.
      * inv MREG ; auto. eapply H2 ; eauto.
        assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
      * ((intros [tf' [Hfind OKtf']]);
         (exists (RTL.Callstate (RTL.Stackframe res tf sp pc' rs' :: ts) 
                                tf' rs' ## args
                                m) ; split;
             [(eapply plus_one; try DStep_tac ; eauto);
               (eapply RTL.exec_Icall  ; eauto); 
               (eauto with valagree)
             | ])).
        assert (HRpc': map_pc (mapping f) pc' = pc')
        by (eapply wf_ninop_id_succ; eauto using transl_function_spec_ok; go).
        rewrite <- HRpc' at 2. clear HRpc'.      
        { erewrite match_regset_args ; eauto.
          econstructor ; auto.
          - unfold ros_to_vos in H0. des_ifs. simpl in H0. eapply Genv.find_funct_prop ; eauto.
            eapply Genv.find_funct_prop ; eauto. instantiate (1 := Vptr b i). ss.
          - unfold ros_to_vos in H0. des_ifs. simpl in H0. eapply Genv.find_funct_prop ; eauto.
            eapply Genv.find_funct_prop ; eauto. instantiate (1 := Vptr b i). ss.
          - assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
        }

    + exploit (spec_ros_id_find_function  rs rs') ; eauto.
      ((intros [tf' [Hfind OKtf']]);
       (exists (RTL.Callstate (RTL.Stackframe res tf sp pc' rs' :: ts) tf' rs' ## args m) ; split;
               [(eapply plus_one; try DStep_tac ; eauto);
                 (eapply RTL.exec_Icall  ; eauto); 
                 (eauto with valagree)
               | ])).
      assert (HRpc': map_pc (mapping f) pc' = pc')
        by (eapply wf_ninop_id_succ; eauto using transl_function_spec_ok; go).
        rewrite <- HRpc' at 2. clear HRpc'.      
        { erewrite match_regset_args ; eauto.
          econstructor ; auto.
          - simpl in H0.
            destruct Genv.find_symbol in H0; try congruence.
            eapply Genv.find_funct_ptr_prop ; eauto.
          - simpl in H0.
            destruct Genv.find_symbol in H0; try congruence.
            eapply Genv.find_funct_ptr_prop ; eauto.
          - assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
        }

  - (* itailcall *)
    normalized pc; allinv_par.
    rewrite H7 in * ; clear H7 ; subst.
    destruct ros.
    + exploit (spec_ros_r_find_function rs rs') ; eauto.
      * inv MREG ; eauto. eapply H3 ; eauto. 
        assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
      * (intros [tf' [Hfind OKtf']]);
        (exploit (sig_function_translated f tf) ; eauto ; intros);
        ((exists (RTL.Callstate ts tf' rs'##args m');  split);
         [  (eapply plus_one; try DStep_tac ; eauto); 
           (eapply RTL.exec_Itailcall ; eauto with valagree);
           (replace (RTL.fn_stacksize tf) with (fn_stacksize f); eauto with valagree)
          | ]).
        { replace (rs' ## args) with (rs## args).
          - econstructor ; eauto.
            simpl in H0.
            + unfold ros_to_vos in H0. des_ifs.
              eapply Genv.find_funct_prop ; eauto. instantiate (1 := Vptr b (Ptrofs.repr z)). ss.
              eapply Genv.find_funct_prop ; eauto. instantiate (1 := Vptr b i). ss.
            + unfold ros_to_vos in H0. des_ifs.
              eapply Genv.find_funct_prop ; eauto.
              eapply Genv.find_funct_prop ; eauto. instantiate (1 := Vptr b i). ss.
          - eapply match_regset_args ; eauto. 
            assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
        }     
    + exploit (spec_ros_id_find_function  rs rs') ; eauto.    
      (intros [tf' [Hfind OKtf']]);
        (exploit (sig_function_translated f tf) ; eauto ; intros);
        ((exists (RTL.Callstate ts tf' rs'##args m');  split);
         [  (eapply plus_one; try DStep_tac ; eauto); 
           (eapply RTL.exec_Itailcall ; eauto with valagree);
           (replace (RTL.fn_stacksize tf) with (fn_stacksize f); eauto with valagree)
          | ]).
      { replace (rs' ## args) with (rs## args).
        econstructor ; eauto.
        - simpl in H0.    
          destruct Genv.find_symbol in H0; try congruence.
          eapply Genv.find_funct_ptr_prop ; eauto.
        - simpl in H0.    
          destruct Genv.find_symbol in H0; try congruence.
          eapply Genv.find_funct_ptr_prop ; eauto.
        - eapply match_regset_args ; eauto.
          assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
      }

  - (* ibuiltin *)
    normalized pc; allinv_par.
    rewrite H7 in * ; clear H7 ; subst. 
    exists  (RTL.State ts tf sp pc' (regmap_setres res vres rs') m'). 
    split.
    + eapply plus_one ; eauto.
      DStep_tac. unfold is_internal in INT. ss. des_ifs.
      eapply RTL.exec_Ibuiltin with (vargs := vargs) ; eauto.
      assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
      { eapply eval_builtin_args_preserved with (ge1 := ge); eauto.
        apply senv_preserved.
        inv MREG. 
        revert H0 HH H. clear.
        induction 1 ; intros; go.
        simpl. constructor.
        - revert H HH H1. clear. induction 1 ; intros; go.
          + simpl. rewrite H1; go.
          + simpl. 
            constructor.
            * eapply IHeval_builtin_arg1; eauto.
              simpl. intros. eapply HH; eauto. simpl.
              eapply in_app_or in H2. 
              eapply in_or_app.  intuition.
              right. eapply in_or_app.
              eapply in_app_or in H3. 
              intuition.
            * eapply IHeval_builtin_arg2; eauto.
              simpl. intros. eapply HH; eauto. simpl.
              eapply in_app_or in H2. 
              eapply in_or_app.  intuition.
              right. eapply in_or_app.
              eapply in_app_or in H3. 
              intuition.
              
          + simpl. 
            constructor.
            * eapply IHeval_builtin_arg1; eauto.
              simpl. intros. eapply HH; eauto. simpl.
              eapply in_app_or in H2. 
              eapply in_or_app.  intuition.
              right. eapply in_or_app.
              eapply in_app_or in H3. 
              intuition.
              
            * eapply IHeval_builtin_arg2; eauto.
              simpl. intros. eapply HH; eauto. simpl.
              eapply in_app_or in H2. 
              eapply in_or_app.  intuition.
              right. eapply in_or_app.
              eapply in_app_or in H3. 
              intuition.
              
        - eapply IHlist_forall2; eauto.
          intros. eapply HH; eauto. simpl.
          eapply in_app_or in H2.
          intuition.
          
      } 
      eapply external_call_symbols_preserved; eauto with valagree.
    + assert (HRpc': map_pc (mapping f) pc' = pc')
        by (eapply wf_ninop_id_succ; eauto using transl_function_spec_ok; go).
      rewrite <- HRpc' at 2. clear HRpc'.      
      econstructor 1 ; eauto. 
      constructor. intros.
      destruct res ; simpl; go.
      * { destruct (peq x r). 
          - inv e. rewrite PMap.gss. rewrite PMap.gss; auto.
          - rewrite PMap.gso; auto. rewrite PMap.gso; auto.
            inv MREG ; auto.
        }
      * inv MREG ; auto.
      * inv MREG ; auto.
      
  - (* ifso *)
    normalized pc; allinv_par.
    rewrite H6 in * ; clear H6 ; subst.
    exists (RTL.State ts tf sp ifso rs' m); split ; eauto. 
    eapply plus_one ; eauto.
    DStep_tac.
    eapply RTL.exec_Icond ; eauto.
    erewrite <- match_regset_args ; eauto with valagree.
    assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
    reflexivity.
    assert (HRpc': map_pc (mapping f) ifso = ifso)
        by (eapply wf_ninop_id_succ; eauto using transl_function_spec_ok; go).
    rewrite <- HRpc' at 2. clear HRpc'.
    econstructor 1 ; eauto.
      
  - (* ifnot *)
    normalized pc; allinv_par.
    rewrite H6 in * ; clear H6 ; subst.
    exists (RTL.State ts tf sp ifnot rs' m); split ; eauto. 
    eapply plus_one ; eauto.  
    DStep_tac.
    eapply RTL.exec_Icond ; eauto. 
    erewrite <- match_regset_args ; eauto with valagree.
    assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
    reflexivity.
    assert (HRpc': map_pc (mapping f) ifnot = ifnot)
        by (eapply wf_ninop_id_succ; eauto using transl_function_spec_ok; go).
    rewrite <- HRpc' at 2. clear HRpc'.
    econstructor 1 ; eauto.

  - (* ijump *)
    normalized pc; allinv_par.
    rewrite H7 in * ; clear H7 ; subst.
    exists (RTL.State ts tf sp pc' rs' m); split ; eauto. 
    + eapply plus_one ; eauto.
      DStep_tac.
      eapply RTL.exec_Ijumptable ; eauto.
      inv MREG. erewrite <- H3 ; eauto.
      assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
    + assert (HRpc': map_pc (mapping f) pc' = pc').
      { eapply wf_ninop_id_succ; eauto using transl_function_spec_ok; go.
        simpl. eapply list_nth_z_in ; eauto.
      }
      rewrite <- HRpc' at 2. clear HRpc'.      
      econstructor 1 ; eauto. 
    
  - (* ireturn *)
    (exploit transl_function_spec_ok ; eauto; intros).
    normalized pc ; allinv_par.
    rewrite H7 in * ; clear H7 ; subst.
    exists (RTL.Returnstate ts (regmap_optget or Vundef rs') m'); split ; eauto. 
    + eapply plus_one ; eauto.
      DStep_tac.
      eapply RTL.exec_Ireturn ; eauto.
      rewrite <- H0 ; eauto with valagree.
      rewrite stacksize_preserved with f tf ; eauto.
    + replace (regmap_optget or Vundef rs') with (regmap_optget or Vundef rs).
      go. unfold regmap_optget.
      destruct or; try reflexivity. 
      inv MREG. rewrite H3 ; eauto. 
      assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.

  - (* internal *)
    simpl in SPEC. Errors.monadInv SPEC. 
    exists (RTL.State ts x
                      (Vptr stk Ptrofs.zero)
                      (RTL.fn_entrypoint x)
                      (RTL.init_regs args (RTL.fn_params x))
                      m').
    inv WF.
    exploit transl_function_spec_ok; eauto. intros SPEC.
    split.
    + eapply plus_one ; eauto.
      DStep_tac.
      eapply RTL.exec_function_internal; eauto.
      rewrite stacksize_preserved with f x in H ; auto.
    + assert ((RTL.fn_entrypoint x) = (map_pc (mapping f) (fn_entrypoint f))).
      { 
        replace (RTL.fn_entrypoint x) with (fn_entrypoint f).
        - symmetry. 
          exploit fn_entry ; eauto. intros [succ Hins].
          eapply wf_njp_id ; eauto.
          intro Hcont.
          invh join_point.
          destruct l. 
          + simpl in *. lia.
          + generalize (KildallComp.make_predecessors_correct2 (fn_code f) successors_instr).
            intros Hcont.
            exploit @KildallComp.make_predecessors_some; eauto.
            intros [ip Hip].
            specialize (Hcont p ip (fn_entrypoint f) Hip).
            eelim fn_entry_pred with (pc := p); eauto. 
            econstructor ; eauto.
            apply Hcont.
            unfold successors_list, KildallComp.make_preds.
            rewrite Hpreds; auto.
        - unfold transl_function in * ; flatten EQ  ; auto.
      }
      rewrite H0. 
      invh mill_fundef.
      econstructor; eauto.       
      constructor. 
      intros. inv SPEC. 
      replace (RTL.fn_params x) with (fn_params f).
      auto. 
      unfold transl_function in * ; flatten EQ ; auto.
  
  - (* external *)
    inv SPEC.
    exists (RTL.Returnstate ts res m'). split. 
    eapply plus_one ; eauto.
    DStep_tac.
    eapply RTL.exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto with valagree.
    econstructor ; eauto.
  
  - (* return state *)
    inv STACK. 
    exists (RTL.State ts0 tf sp (map_pc (mapping f) pc) (rs'# res <- vres) m).
    split. 
    + eapply plus_one ; eauto.
      DStep_tac.
      econstructor.
    + econstructor; eauto. 
      constructor. intros. 
      destruct (peq res r).
      * inv e. rewrite PMap.gss. rewrite PMap.gss; auto.
      * rewrite PMap.gso; auto. rewrite PMap.gso; auto. 
        inv MREG ; auto.
        Unshelve. all: eapply true.
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
  unfold is_external in *. des_ifs. inv MATCH; ss.
  (* builtin *)
  - match goal with 
    | [H : transl_fundef (Internal ?f) = _ |- _ ] => idtac
    | [H : transl_fundef (External ?f) = _ |- _ ] => idtac
    | [  |- context [RTL.Returnstate ?ts ?vres ?m]] => idtac
    | _ => 
        ( (exploit transl_function_spec_ok ; eauto; intros))
    end; 
    try match goal with 
      | [SPEC: transl_function_spec ?f ?tf ?R |- _ ] => 
          generalize SPEC ; inv SPEC ; intros SPEC
      end; allinv_par.
    normalized pc; allinv_par.
    inv STEPTGT; rewrite <- H3, H4 in *; clarify.
    exists (RTLpar.State stack f sp n (regmap_setres b vres rs) m').
    split.
    + eapply exec_Ibuiltin with (vargs := vargs) ; eauto.
      assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
      { eapply eval_builtin_args_preserved. i. symmetry. eapply senv_preserved.
        inv MREG. 
        revert H13 HH H0. clear.
        induction 1 ; intros; go.
        simpl. constructor.
        - revert H HH H0. clear. induction 1 ; intros; go.
          + simpl. rewrite <- H0; go.
          + simpl. 
            constructor.
            * eapply IHeval_builtin_arg1; eauto.
              simpl. intros. eapply HH; eauto. simpl.
              eapply in_app_or in H2. 
              eapply in_or_app.  intuition.
              right. eapply in_or_app.
              eapply in_app_or in H3. 
              intuition.
            * eapply IHeval_builtin_arg2; eauto.
              simpl. intros. eapply HH; eauto. simpl.
              eapply in_app_or in H2. 
              eapply in_or_app.  intuition.
              right. eapply in_or_app.
              eapply in_app_or in H3. 
              intuition.
              
          + simpl. 
            constructor.
            * eapply IHeval_builtin_arg1; eauto.
              simpl. intros. eapply HH; eauto. simpl.
              eapply in_app_or in H2. 
              eapply in_or_app.  intuition.
              right. eapply in_or_app.
              eapply in_app_or in H3. 
              intuition.
              
            * eapply IHeval_builtin_arg2; eauto.
              simpl. intros. eapply HH; eauto. simpl.
              eapply in_app_or in H2. 
              eapply in_or_app.  intuition.
              right. eapply in_or_app.
              eapply in_app_or in H3. 
              intuition.
              
        - eapply IHlist_forall2; eauto.
          intros. eapply HH; eauto. simpl.
          eapply in_app_or in H1.
          intuition.
      }
      eapply external_call_symbols_preserved; eauto with valagree.
    + assert (HRpc': map_pc (mapping f) n = n)
        by (eapply wf_ninop_id_succ; eauto using transl_function_spec_ok; go).
      rewrite <- HRpc' at 2. clear HRpc'.      
      econstructor 1 ; eauto. 
      constructor. intros.
      destruct b ; simpl; go.
      * { destruct (peq x r). 
          - inv e0. rewrite PMap.gss. rewrite PMap.gss; auto.
          - rewrite PMap.gso; auto. rewrite PMap.gso; auto.
            inv MREG ; auto.
        }
      * inv MREG ; auto.
      * inv MREG ; auto.
  (* external *)
  - inv MATCH; ss. inv STEPTGT; try by clarify.
    inv SPEC.
    exists (Returnstate stack res m'). split.
    eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto with valagree.
    econstructor ; eauto.
Qed.

Lemma match_states_xsim
    st_src0 st_tgt0 gmtgt
    (MATCH: match_states st_src0 st_tgt0) :
  xsim (semantics prog) (RTL.semantics tprog) gmtgt lt 0%nat st_src0 st_tgt0.
Proof.
  generalize dependent st_src0. generalize dependent st_tgt0.
  pcofix CIH. i. pfold.
  destruct (classic (is_external ge st_src0)); cycle 1.
  (* not external *)
  - left. econs. econs.
    + i. exploit transl_step_correct; eauto. i. des.
      * esplits; eauto.
        { eapply tr_rel_refl. eapply ev_rel_refl. }
        left. split; eauto.
        eapply RTLparD.semantics_receptive_at; auto.
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
      * match goal with 
        | [H : transl_fundef (Internal ?f) = _ |- _ ] => idtac
        | [H : transl_fundef (External ?f) = _ |- _ ] => idtac
        | [  |- context [RTL.Returnstate ?ts ?vres ?m]] => idtac
        | _ => 
            ( (exploit transl_function_spec_ok ; eauto; intros))
        end; 
        try match goal with 
          | [SPEC: transl_function_spec ?f ?tf ?R |- _ ] => 
              generalize SPEC ; inv SPEC ; intros SPEC
          end; allinv_par.
        normalized pc; allinv_par.
        rewrite H5 in * ; clear H5 ; subst. 
        esplits. eapply RTL.exec_Ibuiltin with (vargs:=vargs); eauto.
        assert (HH:= get_maxreg_is_not_temp_code f pc); flatten HH; eauto.
        { eapply eval_builtin_args_preserved with (ge1 := ge); eauto.
          apply senv_preserved.
          inv MREG. 
          revert H9 HH H1. clear.
          induction 1 ; intros; go.
          simpl. constructor.
          - revert H HH H1. clear. induction 1 ; intros; go.
            + simpl. rewrite H1; go.
            + simpl. 
              constructor.
              * eapply IHeval_builtin_arg1; eauto.
                simpl. intros. eapply HH; eauto. simpl.
                eapply in_app_or in H2. 
                eapply in_or_app.  intuition.
                right. eapply in_or_app.
                eapply in_app_or in H3. 
                intuition.
              * eapply IHeval_builtin_arg2; eauto.
                simpl. intros. eapply HH; eauto. simpl.
                eapply in_app_or in H2. 
                eapply in_or_app.  intuition.
                right. eapply in_or_app.
                eapply in_app_or in H3. 
                intuition.
                
            + simpl. 
              constructor.
              * eapply IHeval_builtin_arg1; eauto.
                simpl. intros. eapply HH; eauto. simpl.
                eapply in_app_or in H2. 
                eapply in_or_app.  intuition.
                right. eapply in_or_app.
                eapply in_app_or in H3. 
                intuition.
                
              * eapply IHeval_builtin_arg2; eauto.
                simpl. intros. eapply HH; eauto. simpl.
                eapply in_app_or in H2. 
                eapply in_or_app.  intuition.
                right. eapply in_or_app.
                eapply in_app_or in H3. 
                intuition.
                
          - eapply IHlist_forall2; eauto.
            intros. eapply HH; eauto. simpl.
            eapply in_app_or in H0.
            intuition.
        }
        eapply external_call_symbols_preserved with (ge1:=ge); eauto.
        eapply senv_preserved.
      * i. inv SPEC.
        esplits. eapply RTL.exec_function_external.
        eapply external_call_symbols_preserved with (ge1:=ge); eauto.
        eapply senv_preserved.
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
    (INITSRC: RTLpar.initial_state prog S1)
    (INITTGT: RTL.initial_state tprog S2)
    (MATCH: match_states S1 S2)
    (CAPTGT: RTL.glob_capture tprog S2 S2'):
  exists S1',
    RTLpar.glob_capture prog S1 S1'
  /\ match_states S1' S2'
  /\ gm_improves (RTLpar.concrete_snapshot ge S1') (RTL.concrete_snapshot tge S2').
Proof.
  specialize senv_preserved. intros SENVEQ. inv CAPTGT. ss.
  rewrite Genv.globalenv_public in CAPTURE.
  rewrite <- same_public in CAPTURE. erewrite <- non_static_equiv in CAPTURE.
  inv MATCH. inv STACK.
  esplits.
  - econs; eauto. rewrite Genv.globalenv_public. eauto.
  - econs; eauto.
  - ii. unfold RTLpar.concrete_snapshot, RTL.concrete_snapshot in *.
    inv SENVEQ. des. erewrite H1, H0. des_ifs; ss.
Qed.

(** * Semantics preservation *)  
Theorem transf_program_correct:
  mixed_simulation (RTLpar.semantics prog) (RTL.semantics tprog).
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
