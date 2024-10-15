(** Specification of RTL normalization *)

Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLnorm.
Require Import Kildall.
Require Import Utils.
Require Import DLib. 
Unset Allow StrictProp.

(** * Specification of a normalized program point *)
Inductive reach_nops (code : code) : node -> node -> list node -> Prop :=
| rp_nil : forall pc pc', 
  code ! pc = Some (Inop pc') -> 
  reach_nops code pc pc' nil
| rp_cons : forall pc0 pc1 pc2 l, 
  reach_nops code pc1 pc2 l -> 
  code ! pc0 = Some (Inop pc1) -> 
  reach_nops code pc0 pc2 (pc1::l).  
  
Variant norm (code code' : code) (pc: node) : Prop :=
| norm_unch : forall ins1 ins2,
      code ! pc = Some ins1 -> 
      code' ! pc = Some ins2 -> 
      ch_succ_dec ins1 ins2 = true -> 
      (forall k succ succ', 
         nth_error (successors_instr ins1) k = Some succ ->
         nth_error (successors_instr ins2) k = Some succ' ->
         (succ' = succ \/ exists aux, reach_nops code' succ' succ aux /\ length aux <= 2)) ->
      norm code code' pc.

(** ** Specification of the translation *)
Variant transl_function_spec: RTL.function -> RTL.function -> Prop :=
  | transl_function_spec_intro: forall f tf aux,
    forall (NORM: forall pc ins, (fn_code f) ! pc = Some ins -> norm (fn_code f) (fn_code tf) pc)
           (ENTRY: reach_nops (fn_code tf) (fn_entrypoint tf) (fn_entrypoint f) aux /\ length aux <= 3),
    transl_function_spec f tf.

(** * Correctness of the checker *)

Lemma forall_list2_nth_error {A : Type} : 
  forall (l1 l2: list A) f k e1 e2, 
    forall_list2 f l1 l2 = true ->
    (length l1) = (length l2) ->
    nth_error l1 k = Some e1 ->
    nth_error l2 k = Some e2 ->
    f e1 e2 = true.
Proof.
  induction l1 ; intros.
  - destruct k ; simpl in *; inv H1. 
  - destruct l2. inv H0.
    destruct k; simpl in * ; boolInv.
    + inv H1. inv H2. auto.
    + eauto.
Qed.

Lemma ch_succ_same_length : forall i i', 
  ch_succ_dec i i' = true ->  
  length  (successors_instr i) = length (successors_instr i').
Proof. 
  destruct i, i'; go. 
  simpl. intros ; boolInv; auto.
Qed.

Lemma inop_tunel_reach_nops : forall code n s1 s2,
    inop_tunel n code s1 s2 = true ->
    (s2 = s1) \/ exists aux, reach_nops code s2 s1 aux /\ length aux <= n - 1.
Proof.
  unfold inop_tunel.
  induction n; intros.
  - rewrite orb_false_r in H.
    destruct peq in H.
    + subst; auto.
    + inv H.
  - fold inop_tunel in *.
    destruct peq in H.
    + subst. auto.
    + rewrite orb_false_l in H.
      flatten H; try congruence.
      subst.
      destruct n.
      * ss. rewrite orb_false_r in H. destruct peq in H.
        { subst. right; exists nil; split; eauto. econs; eauto. }
        { inv H. }
      * eapply IHn in H; eauto.
      inv H.
      { right.
        exists nil.
        split. econstructor; eauto. simpl; lia. }
        { right.
        destruct H0 as [aux [Haux Hlen]].
        exists (n1::aux).
        split; eauto. econstructor; eauto. ss. inv Hlen; try lia. }
Qed.

Lemma check_entry_correct : forall f tf,
    check_entry f tf = true ->
    exists aux, reach_nops (fn_code tf) (fn_entrypoint tf) (fn_entrypoint f) aux /\ length aux <= 3.
Proof.
  unfold check_entry; intros.
  flatten H. subst.
  apply orb_true_iff in H. inv H.
  - destruct peq.
    + subst.
      exists nil.
      split; constructor; auto.
    + inv H0.
  - eapply inop_tunel_reach_nops in H0; eauto.
    inv H0.
    + exists nil.
      split; constructor; auto.
    + destruct H as [aux [Haux Hlen]].
      exists (n::aux).
      split; [econstructor; eauto | simpl; lia].
Qed.

Lemma check_mks_spec_correct: forall code tcode pc i ti,
  code ! pc = Some i ->
  tcode ! pc = Some ti ->
  ch_succ_dec i ti = true ->
  check_mks_spec i ti tcode = true ->
  norm code tcode pc.
Proof.
  unfold check_mks_spec.
  intros until ti ; intros INS TINS CHSUCC CHECK.
  econstructor ; eauto.
  intros k succ succ' SUCC SUCC'.
  exploit ch_succ_same_length; eauto. intros LENGTH.
  exploit @forall_list2_nth_error; eauto.
  eapply inop_tunel_reach_nops; eauto.
Qed.

Lemma checker_correct : forall code tcode pc i,
  checker code tcode = true ->
  code ! pc = Some i ->
  norm code tcode pc.
Proof.
  unfold checker. intros until i ; intros CHECK INS.
  eapply ptree_forall in CHECK; eauto.
  unfold check_pc in *. rewrite INS in *.
  flatten CHECK; try congruence. boolInv.
  eapply check_mks_spec_correct ; eauto ; go.
Qed.    
  
Lemma transl_function_spec_ok : forall f tf, 
  transl_function f = Errors.OK tf -> 
  transl_function_spec f tf.
Proof.
  unfold transl_function ; intros f tf TRANS. 
  flatten TRANS. boolInv. simpl in *.
  eapply check_entry_correct in Eq3; eauto.
  destruct Eq3 as [aux [Hentry Hlen]]. 
  eapply transl_function_spec_intro; eauto.
  intros. eapply checker_correct; eauto.
Qed.
