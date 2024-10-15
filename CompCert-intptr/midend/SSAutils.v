Require Import Coqlib.
Require Import Maps.
Require Import Maps2.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import Floats.
Require Import Kildall. 
Require Import KildallComp.
Require Import SSA.
Require Import Utils.
Require Import Relation_Operators.
Require Import Classical.
Require Import OrderedType.
Require Import Ordered.
Require Import FSets.
Require Import DLib.
Require FSetAVL.
Unset Allow StrictProp.
    
(** * Utility lemmas about [index_pred] *)
Lemma index_pred_some : forall pc t k pc0,
  index_pred t pc0 pc = Some k ->
  (k < length (t!!!pc))%nat.
Proof.
  intros.
  unfold index_pred in H.
  destruct t!!!pc; inv H.
  eapply get_index_some ; eauto.
Qed.  

Lemma index_pred_some_nth: forall pc t k pc0, 
  index_pred t pc0 pc = Some k ->
  nth_error (t!!!pc) k = Some pc0.
Proof.
  intros.
  unfold index_pred in H.
  destruct t !!! pc. 
  inv H.
  eapply get_index_nth_error ; eauto.
Qed.

(** * Utility lemmas about [successors] *)
Lemma successors_instr_succs : forall f pc pc' instr, 
(fn_code f) ! pc = Some instr ->
In pc' (successors_instr instr) ->
exists succs, (successors f) ! pc = Some succs /\ In pc' succs .
Proof.
  intros.
  unfold successors.
  rewrite PTree.gmap1. rewrite H. simpl.
  exists (successors_instr instr) ; auto.
Qed.

Lemma index_pred_instr_some : 
  forall instr pc' f pc  , 
    (fn_code f)!pc = Some instr -> 
    In pc' (successors_instr instr) ->
    (exists k, index_pred (make_predecessors (fn_code f) successors_instr) pc pc' = Some k).
Proof.
  intros. 
  unfold index_pred.
  generalize ((make_predecessors_correct_1 (fn_code f) successors_instr) pc instr pc') ; intros.
  generalize (successors_instr_succs f pc pc' instr H H0) ; intros.
  destruct H2 as [succs [Hsuccs Hinsucc]].
  unfold successors_list in *.
  exploit H1; auto.
  intros.
  case_eq ((make_predecessors (fn_code f) successors_instr) ! pc') ; intros.
  rewrite H3 in *.
  destruct l. inv H2.
  eapply (in_get_index_some) ; eauto.  
  rewrite H3 in H2. inv H2.
Qed.

Lemma get_index_cons_succ: forall x xs k y,
    get_index (x::xs) y = Some (Datatypes.S k) -> get_index xs y = Some k.
Proof.
  intros.
  unfold Utils.get_index in *.
  simpl in *.
  flatten H.
  eapply get_index_some_sn; eauto.
  simpl in *.
  flatten; eauto.
  assert ((k+1)%nat = Datatypes.S k). lia.
  rewrite H0 in *.
  assumption.
Qed.

(** * Utility lemmas about [wf_ssa_function] *)

Lemma no_assigned_phi_spec_fn_entrypoint: forall f,
  wf_ssa_function f -> forall x,
    ~ assigned_phi_spec (fn_phicode f) (fn_entrypoint f) x.
Proof.
  red; intros.
  inv H0.
  assert (join_point (fn_entrypoint f) f).
  { rewrite fn_phicode_inv; auto.
    congruence.
  }
  inv H0. 
  destruct l.
  simpl in Hl; apply False_ind; lia.
  exploit @make_predecessors_some; eauto. intros [pins Hpins].  
  assert (In (fn_entrypoint f) (successors_instr pins)).
  { 
    eapply @make_predecessors_correct2; eauto.
    unfold Kildall.successors_list.
    unfold make_preds.
    rewrite Hpreds.
    left; auto.
  }   
  elim (fn_entry_pred _ H p).
  econstructor; eauto.
Qed.


Lemma fn_phiargs: forall f, 
  wf_ssa_function f -> 
  forall pc block x args pred k, 
    (fn_phicode f) ! pc = Some block -> 
    In (Iphi args x) block -> 
    index_pred (Kildall.make_predecessors (fn_code f) successors_instr) pred pc = Some k ->
    exists arg, nth_error args k = Some arg.
Proof.
  intros. exploit fn_wf_block ; eauto. intros.
  exploit index_pred_some_nth ; eauto.
  intros. eapply nth_error_some_same_length ; eauto.
Qed.
  
Lemma  fn_phicode_code : forall f, 
  wf_ssa_function f ->
  forall pc block, 
    (fn_phicode f) ! pc = Some block -> 
    exists ins, (fn_code f) ! pc = Some ins.
Proof.
  intros.
  generalize (fn_phicode_inv f H pc) ; eauto.
  intros [HH1 HH2].
  exploit HH2; eauto. congruence.
  intros. inv H1.
  
  assert ((make_predecessors (fn_code f) successors_instr) !!! pc = l). 	 
  { unfold successors_list. rewrite Hpreds. auto. }
  assert (exists pred, In pred l). destruct l.  simpl in *. lia. 
  exists p ; eauto. destruct H2. 	 
  exploit @make_predecessors_some; eauto. intros [i Hi].
  assert (In pc (successors_instr i)). 	 
  { eapply make_predecessors_correct2 ; eauto. 	 
    unfold successors_list. 	 
    unfold make_preds. rewrite Hpreds. auto. 
  } 
  
  exploit fn_code_closed ; eauto. 	 
Qed.

Lemma fn_entrypoint_inv: forall f, 
  wf_ssa_function f ->
    (exists i, (f.(fn_code) ! (f.(fn_entrypoint)) = Some i)) /\ 
    ~ join_point f.(fn_entrypoint) f.
Proof.
  intros.   
  exploit fn_entry ; eauto. 
  intros (s & Hentry). 
  split;  eauto.

  intro Hcont. inv Hcont. 
  destruct l. simpl in *. lia.
  
  generalize (make_predecessors_correct2 (fn_code f) successors_instr).
  intros Hcont. 
  exploit @make_predecessors_some; eauto.
  intros [ip Hip].
  specialize (Hcont p ip (fn_entrypoint f) Hip).
  eelim fn_entry_pred with (pc := p); eauto. econstructor ; eauto.
  apply Hcont.
  unfold successors_list, make_preds. 
  rewrite Hpreds; auto.
Qed.  
  
Lemma fn_code_inv2: forall f, 
  wf_ssa_function f -> 
  forall jp pc, (join_point jp f) ->
    In jp ((successors f) !!! pc) ->
    f.(fn_code) ! pc = Some (Inop jp).
Proof.
  intros.
  exploit fn_normalized ; eauto.
Qed.
  
Lemma  fn_phicode_inv1: forall f, 
  wf_ssa_function f ->
  forall phib jp i,
    f.(fn_code) ! jp = Some i -> 
    f.(fn_phicode) ! jp = Some phib ->
    join_point jp f. 
Proof.
  intros. 
  eapply fn_phicode_inv ; eauto. congruence.
Qed.
  
Lemma  fn_phicode_inv2: forall f, 
  wf_ssa_function f -> 
  forall jp i,
    join_point jp f ->
    f.(fn_code) ! jp = Some i -> 
    exists phib, f.(fn_phicode) ! jp = Some phib.
Proof.
  intros. 
  case_eq (fn_phicode f) ! jp ; intros ; eauto.
  destruct (fn_phicode_inv f H jp)  ; eauto.
  eapply H3 in H0. 
  congruence.
Qed.  

Lemma not_jnp_not_assigned_phi_spec: forall f pc y,
  wf_ssa_function f ->
  ~ join_point pc f ->
  ~ assigned_phi_spec (fn_phicode f) pc y.
Proof.
  intros.
  intro Hcont.
  inv Hcont.
  exploit fn_phicode_code ; eauto. intros. inv H3.
  exploit fn_phicode_inv1 ; eauto.
Qed.

Lemma ssa_def_dom_use : forall f,
  wf_ssa_function f -> 
  forall  x u d, use f x u -> def f x d -> dom f d u.
Proof.
  intros. eapply fn_strict ; eauto.
Qed.

Lemma ssa_use_exists_def : forall f,
  wf_ssa_function f -> 
  forall x u,
  use f x u -> exists d, def f x d.
Proof.
  intros.
  destruct (classic (exists pc, assigned_code_spec (fn_code f) pc x)).
  destruct H1 ; eauto.
  destruct (classic (exists pc, assigned_phi_spec (fn_phicode f) pc x)).
  destruct H2 ; eauto.
  exists (fn_entrypoint f) ; eauto.
  econstructor ; eauto.
  econstructor 2 ; eauto.
Qed.  

Lemma wf_ssa_reached : forall f,
  wf_ssa_function f ->
  forall  pc ins, 
  (fn_code f) ! pc = Some ins ->
  reached f pc.
Proof.
  intros. inv H ; eauto.
Qed.
Global Hint Resolve wf_ssa_reached: core.

Lemma ssa_def_use_code_false : forall f,
  wf_ssa_function f ->
  forall x pc,
  use_code f x pc ->
  assigned_code_spec (fn_code f) pc x ->
  False.
Proof.
  intros. eapply fn_use_def_code ; eauto.
Qed.
  
Lemma ssa_not_Inop_not_phi : forall f,
  wf_ssa_function f ->
  forall pc x pc' ins,
  In pc' (successors_instr ins) ->
  (fn_code f) ! pc = Some ins ->
  (forall n, ins <> Inop n) ->
  ~ assigned_phi_spec (fn_phicode f) pc' x.
Proof.
  intros.
  intro Hcont. inv Hcont. 
  exploit fn_phicode_code ; eauto. intros [ins' Hins].
  exploit fn_phicode_inv1 ; eauto. intros Hjp.
  exploit (fn_code_inv2 f H pc' pc) ; eauto.
  unfold successors. simpl.
  unfold Kildall.successors_list.
  rewrite PTree.gmap1 ; eauto.
  unfold option_map. rewrite H1. auto. 
  congruence. 
Qed.

Lemma unique_def_spec_def : forall f x d1 d2
  (HWF: wf_ssa_function f),
  def f x d1 ->
  def f x d2 ->
  d1 <> d2 -> False.
Proof.
  intros. 
  destruct (fn_ssa f) as [Hssa1 Hssa2]; auto.
  generalize (fn_entry f HWF) ; intros. destruct H2 as [succ Hentry].
  generalize (fn_ssa_params f HWF); intros Hparams.
  inv H ; inv H0;  inv H ; inv H2;
    try solve [
    intuition
    | exploit Hparams ; eauto
    | exploit Hparams ; eauto ; (intuition; go)
    | exploit H3 ; eauto 
    | exploit H4 ; eauto; intuition auto
    |   (eelim (Hssa1 x d1 d2) ; eauto; intuition auto ; eauto)].
Qed.  

Lemma def_def_eq : forall f x d1 d2
  (HWF: wf_ssa_function f),
  def f x d1 ->
  def f x d2 ->
  d1 = d2.
Proof.
  intros.
  destruct (peq d1 d2) ; auto.
  eelim (unique_def_spec_def f x d1 d2) ; eauto.
Qed.  

Ltac def_def f x pc pc' :=
  match goal with 
    | [HWF: wf_ssa_function f |- _ ] =>
      (exploit (def_def_eq f x pc pc' HWF); eauto); 
      try (econstructor ; eauto);
        try (solve [econstructor ; eauto])
  end.

Require RTL.
Ltac allinv := 
  repeat 
    match goal with 
      | [ H1:   (fn_code ?tf) ! ?pc = Some _  ,
        H2: (fn_code ?tf) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1:   (RTL.fn_code ?tf) ! ?pc = Some _  ,
        H2: (RTL.fn_code ?tf) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1:   (fn_phicode ?tf) ! ?pc = Some _  ,
        H2: (fn_phicode ?tf) ! ?pc = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1: ?Γ ! ?pc =  _  ,
        H2: ?Γ ! ?pc =  _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | [ H1: index_pred  _ ?pc ?pc' = Some _  ,
        H2: index_pred  _ ?pc ?pc' = Some _ |- _ ] =>
      rewrite H1 in H2; inv H2
      | _ => idtac
    end.

Lemma ssa_def_unique : forall f x d1 d2,
  wf_ssa_function f -> def f x d1 -> def f x d2 -> d1 = d2.
Proof.
  intros.
  def_def f x d1 d2.
Qed.

Lemma assigned_code_and_phi: forall f,
  wf_ssa_function f -> forall r pc pc',
    assigned_code_spec (fn_code f) pc r ->
    assigned_phi_spec (fn_phicode f) pc' r -> False.
Proof.
  intros f WFF r pc pc' H1 H2.
  destruct (fn_ssa _ WFF) as [T _].
  destruct (T r pc pc'); intuition.
Qed.

Lemma assigned_code_unique : forall f,
  wf_ssa_function f -> forall r pc pc',
    assigned_code_spec (fn_code f) pc r ->
    assigned_code_spec (fn_code f) pc' r -> pc=pc'.
Proof.
  intros f WFF r pc pc' H1 H2.
  destruct (fn_ssa _ WFF) as [T _].
  destruct (T r pc pc'); intuition.
Qed.

Lemma assigned_phi_spec_join_point : forall f x pc,
  wf_ssa_function f -> 
  assigned_phi_spec (fn_phicode f) pc x ->
  join_point pc f.
Proof.
  intros.
  inv H0.
  exploit fn_phicode_code; eauto.
  intros [ins Hi].
  eapply fn_phicode_inv1; eauto.
Qed.

Lemma wf_ssa_use_and_def_same_pc : forall f x pc,
  wf_ssa_function f ->
  use f x pc ->
  def f x pc ->
  assigned_phi_spec (fn_phicode f) pc x \/ ext_params f x.
Proof.
  intros f x pc Hw Hu Hd.
  inv Hd; auto.
  inv Hu.
  eelim fn_use_def_code; eauto.
  inv H0.
  exploit fn_phicode_code; eauto; intros [ins Hins].
  exploit fn_phicode_inv1; eauto; intros Hj.
  exploit index_pred_some_nth; eauto.
  intros T.
  eapply nth_error_in in T; eauto.
  exploit (fn_code_inv2 f Hw pc0 pc); eauto.
  
  assert (exists i, (fn_code f) ! pc = Some i ) by (inv H; eauto).
  destruct H0 as (i & Hi).
  
  generalize (make_predecessors_correct2 (fn_code f) successors_instr pc i pc0 Hi); eauto.
  intros HH. 
  unfold successors, successors_list. rewrite PTree.gmap1. 
  unfold option_map. rewrite Hi. 
  apply HH; auto.
  intros Hnop.
  inv H; try congruence.
Qed.

(** * Properties and more lemmas about well-formed SSA functions *)
Section WF_SSA_PROP.

Variable f: function.
Hypothesis HWF : wf_ssa_function f.
Hint Resolve HWF: core.

Lemma elim_structural : forall pc pc' instr instr' block,
    (fn_code f)! pc = Some instr ->
    (fn_code f)! pc' = Some instr' ->
    (fn_phicode f)!pc' = Some block ->
    In pc' (successors_instr instr) ->
    instr = Inop pc'.
Proof.
  intros.
  assert (Hjp : join_point pc' f).
  eapply (fn_phicode_inv1 _) with (phib := block); eauto.
  exploit (fn_code_inv2 _ HWF pc' pc) ; eauto.
  unfold successors_list.
  unfold successors.
  rewrite PTree.gmap1.
  unfold option_map. simpl. rewrite H. auto.
  intros. simpl in *; congruence.
Qed.

Lemma phicode_joinpoint: forall  pc block i,
  (fn_code f) ! pc = Some i ->
  (fn_phicode f) ! pc = Some block ->
  join_point pc f.
Proof.
  intros.
  eapply (fn_phicode_inv1 _) ; eauto.
Qed.

Lemma nophicode_nojoinpoint: forall pc i,
  (fn_code f) ! pc = Some i ->
  (fn_phicode f) ! pc = None ->
  ~ join_point pc f.
Proof.
  intros.
  intro.
  exploit (fn_phicode_inv2 _ HWF); eauto. intros.
  destruct H2. simpl in *.
  congruence.
Qed.

Lemma join_point_exclusive: forall pc i,
  (fn_code f) ! pc = Some i ->
  ~ join_point pc f \/  join_point pc f.
Proof.
  intros.
  case_eq ((fn_phicode f) ! pc); intros.
  right ; eapply phicode_joinpoint; eauto.
  left ; eapply nophicode_nojoinpoint; eauto.
Qed.


Lemma use_ins_code : forall pc x, 
  use f x pc ->
  exists ins, (fn_code f) ! pc = Some ins.
Proof.
  intros. inv H.
  inv H0 ; eauto.
  inv H0. 
  assert (join_point pc0 f) by ( eapply fn_phicode_inv; eauto; congruence).
  inv H.
  exploit index_pred_some_nth; eauto. intros. 
  exploit nth_error_some_in ; eauto. intros.
  exploit @make_predecessors_some; eauto.
  unfold successors_list in H0. rewrite Hpreds in H0. auto.
Qed.

Lemma use_reached : forall pc x, 
  use f x pc ->
  reached f pc.
Proof.
  intros.
  exploit use_ins_code ; eauto.
  intros [ins Hins]. 
  inv HWF.
  eapply fn_code_reached ; eauto.  
Qed.

End WF_SSA_PROP.

(** * Auxiliary semantics for phi-blocks *)

(** Lemmas about the sequential semantics of phiblocks *)
Lemma notin_cons_notin : forall dst block a,
  (forall args, ~ In (Iphi args dst) (a:: block)) ->
  forall args, ~ In (Iphi args dst) block.
Proof. 
  intros. 
  intro ; exploit (H args); eauto. 
Qed.
Global Hint Resolve notin_cons_notin: core.
    
Lemma phi_store_notin_preserved: forall k  block rs dst,
  (forall args, ~ (In (Iphi args dst) block)) ->
    (phi_store k block rs)# dst = rs# dst.
Proof.
  induction block; intros.
  (* *) simpl; auto.
  (* *) destruct a; simpl. 
        case_eq (nth_error l k); intros; eauto.
        (* case some *)
        rewrite PMap.gso ; eauto.
        intro Hinv; subst; exploit (H l); eauto. 
Qed.

(** * How to compute the list of registers of a SSA function. *)
Module SSARegSet := FSetAVL.Make OrderedPositive.

Definition all_def (c:code) (phic: phicode) : SSARegSet.t :=
  PTree.fold
    (fun s _ ins =>
      match ins with
        | Iop op args dst succ => SSARegSet.add dst s
        | Iload chunk addr args dst succ => SSARegSet.add dst s
        | Icall sig fn args dst succ => SSARegSet.add dst s
        | Ibuiltin fn args (BR dst) succ => SSARegSet.add dst s
        | _ => s
      end) c
    (PTree.fold
      (fun s _ phib => 
        List.fold_left 
        (fun s (phi:phiinstruction) => let (_,dst) := phi in SSARegSet.add dst s)
        phib s) phic SSARegSet.empty).

Definition param_set (params: list reg) : SSARegSet.t :=
  List.fold_right SSARegSet.add SSARegSet.empty params.  

Definition all_uses (c: code) (phic: phicode) : SSARegSet.t :=
  PTree.fold
    (fun s _ ins =>
      match ins with
        | Iop op args dst _ => fold_right SSARegSet.add s args
        | Iload chk adr args dst _ => fold_right SSARegSet.add s args
        | Icond cond args _ _ => fold_right SSARegSet.add s args
        | Ibuiltin ef args dst _ => fold_right SSARegSet.add s (params_of_builtin_args args)
        | Istore chk adr args src _ => fold_right SSARegSet.add s (src::args)
        | Icall sig (inl r) args dst _ => fold_right SSARegSet.add s (r::args)
        | Itailcall sig (inl r) args => fold_right SSARegSet.add s (r::args)
        | Icall sig (inr id) args dst _ => fold_right SSARegSet.add s args
        | Itailcall sig (inr id) args => fold_right SSARegSet.add s args
        | Ijumptable arg tbl => SSARegSet.add arg s
        | Ireturn (Some arg) => SSARegSet.add arg s
        | _ => s
      end) c 
    (PTree.fold
      (fun s _ phib => 
        fold_left 
        (fun s (phi:phiinstruction) => 
          let (args,dst) := phi in 
            fold_right SSARegSet.add s args)
        phib s) phic SSARegSet.empty).

Lemma In_fold_right_add1: forall x l a,
 In x l -> SSARegSet.In x (fold_right SSARegSet.add a l).
Proof.
  induction l; simpl; auto.
  intuition.
  destruct 1; subst.
  apply SSARegSet.add_1; auto.
  apply SSARegSet.add_2; auto.
Qed.

Lemma In_fold_right_add2: forall x l a,
  SSARegSet.In x a -> SSARegSet.In x (fold_right SSARegSet.add a l).
Proof.
  induction l; simpl; auto; intros.
  apply SSARegSet.add_2; auto.
Qed.

Lemma In_fold_right_add3: forall x l a,
  SSARegSet.In x (fold_right SSARegSet.add a l) -> SSARegSet.In x a \/ In x l.
Proof.
  induction l; simpl; auto; intros.
  destruct (peq x a); subst; auto.
  destruct (IHl a0); auto.
  eapply SSARegSet.add_3; eauto.
Qed.

Lemma in_all_uses1: forall x pc code s ins,
  code!pc = Some ins ->
      match ins with
        | Iop op args dst _ => In x args
        | Iload chk adr args dst _ => In x args
        | Icond cond args _ _ => In x args
        | Ibuiltin ef args dst _ => In x (params_of_builtin_args args)
        | Istore chk adr args src _ => In x (src::args)
        | Icall sig (inl r) args dst _ => In x (r::args)
        | Itailcall sig (inl r) args => In x (r::args)
        | Icall sig (inr id) args dst _ => In x args
        | Itailcall sig (inr id) args => In x args
        | Ijumptable arg tbl => x = arg 
        | Ireturn (Some arg) => x = arg
        | _ => False
      end ->
  SSARegSet.In x 
  (PTree.fold
    (fun s _ ins =>
      match ins with
        | Iop op args dst _ => fold_right SSARegSet.add s args
        | Iload chk adr args dst _ => fold_right SSARegSet.add s args
        | Icond cond args _ _ => fold_right SSARegSet.add s args
        | Ibuiltin ef args dst _ => fold_right SSARegSet.add s (params_of_builtin_args args)
        | Istore chk adr args src _ => fold_right SSARegSet.add s (src::args)
        | Icall sig (inl r) args dst _ => fold_right SSARegSet.add s (r::args)
        | Itailcall sig (inl r) args => fold_right SSARegSet.add s (r::args)
        | Icall sig (inr id) args dst _ => fold_right SSARegSet.add s args
        | Itailcall sig (inr id) args => fold_right SSARegSet.add s args
        | Ijumptable arg tbl => SSARegSet.add arg s
        | Ireturn (Some arg) => SSARegSet.add arg s
        | _ => s
      end) code s).
Proof.
  intros x pc code s.
  apply PTree_Properties.fold_rec with (P:=
    (fun code s => forall ins,
      code ! pc = Some ins ->
      match ins with
        | Inop _ => False
        | Iop _ args _ _ => In x args
        | Iload _ _ args _ _ => In x args
        | Istore _ _ args src _ => In x (src::args)
        | Icall _ (inl r) args _ _ => In x (r :: args)
        | Icall _ (inr _) args _ _ => In x args
        | Itailcall _ (inl r) args => In x (r :: args)
        | Itailcall _ (inr _) args => In x args
        | Ibuiltin _ args _ _ => In x (params_of_builtin_args args)
        | Icond _ args _ _ => In x args
        | Ijumptable arg _ => x = arg
        | Ireturn (Some arg) => x = arg
        | Ireturn None => False
      end -> SSARegSet.In x s)).
  intros.
  rewrite <- H in H1; eauto.
  intros; rewrite PTree.gempty in *; congruence.
  intros.
  rewrite PTree.gsspec in *; destruct peq; subst.
  inv H2.  
  destruct ins; try contradiction; try (apply In_fold_right_add1; auto).
  destruct s1; apply In_fold_right_add1; auto.
  destruct s1; apply In_fold_right_add1; auto.
  subst; apply SSARegSet.add_1; auto.
  destruct o; try contradiction.
  subst; apply SSARegSet.add_1; auto.
  destruct v; try (destruct s1); try (apply In_fold_right_add2); try (apply H1 with ins; auto).
  apply SSARegSet.add_2; eauto.
  destruct o ; eauto.
  apply SSARegSet.add_2; eauto.
Qed.

Lemma in_all_uses2: forall x code s,
  SSARegSet.In x s ->
  SSARegSet.In x 
  (PTree.fold
    (fun s _ ins =>
      match ins with
        | Iop op args dst _ => fold_right SSARegSet.add s args
        | Iload chk adr args dst _ => fold_right SSARegSet.add s args
        | Icond cond args _ _ => fold_right SSARegSet.add s args
        | Ibuiltin ef args dst _ => fold_right SSARegSet.add s (params_of_builtin_args args)
        | Istore chk adr args src _ => fold_right SSARegSet.add s (src::args)
        | Icall sig (inl r) args dst _ => fold_right SSARegSet.add s (r::args)
        | Itailcall sig (inl r) args => fold_right SSARegSet.add s (r::args)
        | Icall sig (inr id) args dst _ => fold_right SSARegSet.add s args
        | Itailcall sig (inr id) args => fold_right SSARegSet.add s args
        | Ijumptable arg tbl => SSARegSet.add arg s
        | Ireturn (Some arg) => SSARegSet.add arg s
        | _ => s
      end) code s).
Proof.
  intros x code s0.
  apply PTree_Properties.fold_rec with (P:=
    (fun code s => SSARegSet.In x s0 -> SSARegSet.In x s)); auto.
  intros.
  destruct v; auto; try (apply In_fold_right_add2; auto).
  destruct s1; apply In_fold_right_add2; auto.
  destruct s1; apply In_fold_right_add2; auto.
  apply SSARegSet.add_2; eauto.
  destruct o ; eauto.
  apply SSARegSet.add_2; eauto.
Qed.  

Lemma in_all_uses3 : forall x code s pc phib args dst,
  code!pc = Some phib ->
  In (Iphi args dst) phib ->
  In x args ->
   SSARegSet.In x
     (PTree.fold
        (fun (s : SSARegSet.t) (_ : positive) (phib : list phiinstruction) =>
         fold_left
           (fun (s0 : SSARegSet.t) (phi : phiinstruction) =>
            let (args, _) := phi in fold_right SSARegSet.add s0 args) phib s)
        code s).
Proof.
  intros x code s.
  apply PTree_Properties.fold_rec with (P:=
    (fun code s =>  forall pc phib args dst,
      code ! pc = Some phib ->
      In (Iphi args dst) phib ->
      In x args ->
      SSARegSet.In x s)); intros; auto.
  rewrite <- H in *; eauto.
  rewrite PTree.gempty in *; congruence.
  assert (forall phib a,
    SSARegSet.In x a ->
    SSARegSet.In x
    (fold_left
      (fun (s0 : SSARegSet.t) (phi : phiinstruction) =>
        let (args0, _) := phi in fold_right SSARegSet.add s0 args0) phib a)).
    induction phib0; simpl; auto.
    intros; apply IHphib0; auto.
    destruct a0.
    apply In_fold_right_add2; auto.    
  rewrite PTree.gsspec in *; destruct peq; subst.
  inv H2.
  clear H0 H1 H.  
  generalize dependent args.
  generalize dependent dst.
  generalize dependent a.
  generalize dependent phib.
  induction phib; simpl; intuition.
  subst.
  apply H5.
  apply In_fold_right_add1; auto.    
  eapply IHphib; eauto.
  apply H5; eauto.
Qed.


Definition ext_params_list (c: code) (phic: phicode) (params: list reg) : list reg :=
  SSARegSet.elements 
  (SSARegSet.diff (all_uses c phic)
    (SSARegSet.union (all_def c phic) (param_set params)))
++params.

Lemma In_param_set : forall l x, SSARegSet.In x (param_set l) -> In x l.
Proof.
  unfold param_set; intros.
  elim In_fold_right_add3 with (1:=H); auto; intros.
  elim SSARegSet.empty_1 with (1:=H0).
Qed.

Lemma use_In_all_usses : forall f x pc,
  use f x pc -> SSARegSet.In x (all_uses (fn_code f) (fn_phicode f)).
Proof.
  intros.
  inv H.
  unfold all_uses.
  inv H0;
  eapply in_all_uses1; simpl; eauto.
  simpl; auto.
  simpl; auto.
  unfold all_uses.
  eapply in_all_uses2; simpl; eauto.
  inv H0.
  eapply in_all_uses3; simpl; eauto.
  eapply nth_error_in; eauto.
Qed.

Lemma In_all_def1: forall x code s,
  SSARegSet.In x
  (PTree.fold
    (fun (s : SSARegSet.t) (_ : positive) (ins : instruction) =>
      match ins with
        | Inop _ => s
        | Iop _ _ dst _ => SSARegSet.add dst s
        | Iload _ _ _ dst _ => SSARegSet.add dst s
        | Istore _ _ _ _ _ => s
        | Icall _ _ _ dst _ => SSARegSet.add dst s
        | Itailcall _ _ _ => s
        | Ibuiltin _ _ (BR dst) _ => SSARegSet.add dst s
        | Ibuiltin _ _ _ _ => s
        | Icond _ _ _ _ => s
        | Ijumptable _ _ => s
        | Ireturn _ => s
      end) code s) ->
  SSARegSet.In x s \/
  exists pc : node, assigned_code_spec code pc x.
Proof.
  intros x code s0.
  apply PTree_Properties.fold_rec with (P:=fun code s =>
    SSARegSet.In x s ->
    SSARegSet.In x s0 \/ (exists pc : node, assigned_code_spec code pc x)).
  - intros.
    destruct (H0 H1); auto.
    destruct H2 as [pc H2]; right.
    exists pc; inv H2; rewrite H in *; eauto.
  - auto.
  - 
    intros.
    destruct v;try destruct (H1 H2); auto.
    + destruct H3 as [pc H3]; right; exists pc.
      inv H3.
      * econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      * econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      * econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      * econstructor 4; go; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
    + destruct (peq x r).
      * subst; right; exists k; econstructor; eauto.
        rewrite PTree.gss; eauto.
      * { elim H1; auto.
          - destruct 1 as [pc T].
            right; exists pc; inv T.
            + econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
            + econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
            + econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
            + econstructor 4; go; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
          - eapply SSARegSet.add_3; eauto.
            
        }
    + destruct (peq x r).
      subst; right; exists k; econstructor 2; eauto.
      rewrite PTree.gss; eauto.
      elim H1; auto.
      destruct 1 as [pc T].
      right; exists pc; inv T.
      econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 4; go; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      eapply SSARegSet.add_3; eauto.
      
    + destruct H3 as [pc H3]; right; exists pc.
      inv H3.
      econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 4; go; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
    + destruct (peq x r).
      subst; right; exists k; econstructor 3; eauto.
      rewrite PTree.gss; eauto.
      elim H1; auto.
      destruct 1 as [pc T].
      right; exists pc; inv T.
      econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 4; go; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      eapply SSARegSet.add_3; eauto.
      
    + destruct H3 as [pc H3]; right; exists pc.
      inv H3.
      econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 4; go; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
    + case_eq b; intros; subst.
      * destruct (peq x0 x).
        subst; right; exists k; econstructor 4; go. 
        rewrite PTree.gss; go. 
        elim H1; auto.
        destruct 1 as [pc T].
        right; exists pc; inv T.
        econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
        econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
        econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
        econstructor 4; go; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
        eapply SSARegSet.add_3; eauto.
        
      * elim H1; auto.
        destruct 1 as [pc T].
        right; exists pc; inv T.
        econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
        econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
        econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
        econstructor 4; go; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      * elim H1; auto.
        destruct 1 as [pc T].
        right; exists pc; inv T.
        econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
        econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
        econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
        econstructor 4; go; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
    + elim H1; auto.
      destruct 1 as [pc T].
      right; exists pc; inv T.
      econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 4; go; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
    + destruct H3 as [pc H3]; right; exists pc.
      inv H3.
      econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 4; go; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
    + destruct H3 as [pc H3]; right; exists pc.
      inv H3.
      econstructor 1; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 2; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 3; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
      econstructor 4; go; rewrite PTree.gsspec; destruct peq; eauto; subst; congruence.
Qed.

Lemma In_fold_left_add1 : forall x phib s,
  SSARegSet.In x (fold_left (fun s0 (phi:phiinstruction) =>  let (_, dst) := phi in SSARegSet.add dst s0) phib s) ->
  SSARegSet.In x s \/ exists args, In (Iphi args x) phib.
Proof.
  induction phib; simpl; auto; intros.
  elim IHphib with (1:=H); clear IHphib; intros.
  destruct a.
  destruct (peq x r); subst; eauto.
  left; eapply SSARegSet.add_3; eauto.
  destruct H0; eauto.
Qed.

Lemma In_all_def2: forall x p s,
   SSARegSet.In x
     (PTree.fold
        (fun (s : SSARegSet.t) (_ : positive) (phib : list phiinstruction) =>
         fold_left
           (fun (s0 : SSARegSet.t) (phi : phiinstruction) =>
            let (_, dst) := phi in SSARegSet.add dst s0) phib s) p
        s) -> 
     SSARegSet.In x s \/
     exists pc : node, assigned_phi_spec p pc x.
Proof.
  intros x p s0.
  apply PTree_Properties.fold_rec with (P:=fun code s =>
    SSARegSet.In x s -> 
     SSARegSet.In x s0 \/
     exists pc : node, assigned_phi_spec p pc x); auto.
  intros.
  elim In_fold_left_add1 with (1:=H2); clear H2; intros H2.
  destruct H1; auto.
  right; exists k; econstructor; eauto.
Qed.

Lemma In_all_def : forall f x,
  SSARegSet.In x (all_def (fn_code f) (fn_phicode f)) ->
  (exists pc, assigned_phi_spec (fn_phicode f) pc x)
  \/ (exists pc, assigned_code_spec (fn_code f) pc x).
Proof.
  intros; unfold all_def in *.
  destruct In_all_def1 with (1:=H); eauto.
  clear H; left.
  elim In_all_def2 with (1:=H0); auto; intros.
  elim SSARegSet.empty_1 with (1:=H).
Qed.

Lemma InA_In : forall x (l:list reg),
  InA (fun a b : OrderedPositive.t => a = b) x l <-> In x l.
Proof.
  induction l; simpl; split; intros; inv H.
  - auto.
  - rewrite IHl in H1; auto.
  - constructor 1 ;auto.
  - constructor 2; auto.
    rewrite IHl; auto.
Qed.

Lemma ext_params_list_spec : forall f x,
    ext_params f x ->
    In x (ext_params_list (fn_code f) (fn_phicode f) (fn_params f)).
Proof.
  unfold ext_params_list; intros f x H.
  inv H.
  - auto with datatypes.
  - destruct (classic (In x (fn_params f))) as [E|E].
    + rewrite in_app; right; auto.
    + rewrite in_app; left.
      eapply InA_In.
      apply SSARegSet.elements_1.
      apply SSARegSet.diff_3.
      * destruct H0; eapply use_In_all_usses; eauto.
      * intro.
        elim SSARegSet.union_1 with (1:=H); clear H; intros H.
        elim In_all_def with (1:=H); intros [pc T]; intuition eauto.
        elim E.
        apply In_param_set; auto.
Qed.

Lemma unique_def_elim1: forall f pc pc' x, 
  unique_def_spec f ->
  assigned_code_spec (fn_code f) pc x ->
  assigned_phi_spec (fn_phicode f) pc' x -> 
  False.
Proof.
  intros. inv H.
  generalize (H2 x pc pc') ; intros Hcont.  
  intuition.
Qed.

  Ltac ssa_def := 
    let eq_pc pc1 pc2 := 
    assert (pc1 = pc2) by (eapply ssa_def_unique; eauto); subst
    in
    match goal with 
      | r : reg |- _ =>
            match goal with 
               id: def _ r ?x,
               id': def _ r ?y
               |- _ => eq_pc x y ; try clear id'
            end
      | pc1: node,
        pc2: node |- _ =>
            match goal with 
                id : def _ ?r pc1,
                id': assigned_phi_spec _ pc2 ?r |- _ =>
                eq_pc pc1 pc2
            end
      |  pc1: node,
         pc2: node |- _ =>
            match goal with 
                id: assigned_phi_spec _ pc1 ?r,
                id': assigned_phi_spec _ pc2 ?r |- _ =>
                eq_pc pc1 pc2
            end
      | id : _ ! ?pc1 = Some (Iop _ _ ?r _),
        id' : _ ! ?pc2 = Some (Iop _ _ ?r _)
        |- _ => 
        match pc2 with
          | pc1 => fail 1
          | _ => idtac
        end;
          eq_pc pc1 pc2
      | id : _ ! ?pc1 = Some (Iop _ _ ?r _),
        id': def _ ?r ?pc2 |- _ =>
        match pc2 with
          | pc1 => fail 1
          | _ => idtac
        end;
          eq_pc pc1 pc2
      end.

  (** ** The [is_edge] predicate *)
Variant is_edge (tf:SSA.function) : node -> node -> Prop:=
| Edge: forall i j instr, 
  (fn_code tf)!i = Some instr ->
  In j (successors_instr instr) ->
  is_edge tf i j.

Lemma is_edge_pred: forall tf i j,
  is_edge tf i j ->
  exists k, index_pred  (make_predecessors (fn_code tf) successors_instr) i j = Some k.
Proof.
  intros. inv H. 
  eapply index_pred_instr_some ; eauto.
Qed.

Lemma pred_is_edge_help: forall tf i j k,
  index_pred  (make_predecessors (fn_code tf) successors_instr) i j = Some k -> 
  (is_edge tf i j).
Proof.
  intros. 
  unfold index_pred in *. 
  case_eq ((make_predecessors (fn_code tf) successors_instr) !!! j); intros ; rewrite H0 in *.
  - inv H.
  - exploit get_index_some_in ; eauto ; intros.
    rewrite <- H0 in *.
    exploit (make_predecessors_some (fn_code tf) successors_instr j); eauto.
    unfold make_preds, successors_list in *.
    destruct ((make_predecessors (fn_code tf) successors_instr) ! j).
    auto. inv H1.
    intros (ins & Hins).
    assert (Hcorr := make_predecessors_correct2 (fn_code tf) successors_instr i ins j Hins H1); auto. 
    eapply Edge; eauto. 
Qed.
  
Lemma pred_is_edge: forall tf i j k,
                      index_pred (make_predecessors (fn_code tf) successors_instr) i j = Some k -> is_edge tf i j.
Proof.
  intros. 
  exploit_dstr pred_is_edge_help; eauto.
Qed.

Variant ssa_def : Type := 
| SDIop (pc:node)
| SDPhi (pc:node) (idx:nat).

Variant ssa_eq : Type := 
| EqIop (op:operation) (args:list reg) (dst:reg)
| EqPhi (dst:reg) (args:list reg).

Definition ssa_eq_to_dst (eq:ssa_eq) : reg :=
  match eq with
    | EqIop _ _ dst => dst
    | EqPhi dst _ => dst
  end.

Definition get_ssa_eq (f:function) (d:ssa_def) : option ssa_eq :=
  match d with
    | SDIop pc => 
      match (fn_code f)!pc with
        | Some (Iop op args dst _) => Some (EqIop op args dst)
        | _ => None
      end
    | SDPhi pc idx =>
      match (fn_phicode f)!pc with
        | Some phi =>
          match nth_error phi idx with
            | Some (Iphi args dst) => Some (EqPhi dst args)
            | None => None
          end
        | _ => None
      end
  end.
