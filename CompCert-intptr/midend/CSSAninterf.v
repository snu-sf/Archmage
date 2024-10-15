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
Require Import CSSAval.
Require Import RTLpargen.
Require Import CSSAutils.
Require Import CSSAdef.
Require Import Registers.

Unset Allow StrictProp.

(** Interference *)

Variant ninterfere_spec (f : function) (r1 r2 : reg) : Prop :=
| ninterfere_spec_ssaval :
    cssaval_spec f (compute_cssaval_function f) ->
    compute_cssaval_function f r1 = compute_cssaval_function f r2 ->
    ninterfere_spec f r1 r2
| ninterfere_spec_liverange :
    ninterlive_spec f r1 r2 ->
    ninterfere_spec f r1 r2.

Lemma test_ninterlive_correct :
  forall f lv r1 r2 d1 d2 def
         (WFF: wf_cssa_function f),
  CSSAlive.analyze f = Some lv ->
  compute_def f (get_all_def f) = def ->
  CSSA.def f r1 d1 ->
  CSSA.def f r2 d2 ->
  negb
    ((peq (def r1) (def r2)) ||
     SSARegSet.mem r1
      (PMap.get (def r2) lv) ||
    (SSARegSet.mem r2
      (PMap.get (def r1) lv))) = true ->
  ninterlive_spec f r1 r2.
Proof.
  intros until def.
  intros WFF Hlive Hcdef Hdefr1 Hdefr2 Htest.
  assert (WF: CSSAlive.wf_live f (CSSAlive.Lout lv))
   by (eapply CSSAlive.live_wf_live; eauto).
  unfold CSSAlive.wf_live in WF.
  destruct peq in Htest; go.
  unfold negb in Htest.
  flatten Htest.
  simpl in *.
  econstructor; eauto; rewrite <- Hcdef in *;
  assert(EQ1: compute_def f (get_all_def f) r1 = d1) by
    (apply compute_def_correct; auto);
  rewrite EQ1 in *;
  assert(EQ2: compute_def f (get_all_def f) r2 = d2) by
    (apply compute_def_correct; auto);
  rewrite EQ2 in *;
  match goal with
  | [H: _ |- d1 <> d2 ] =>
      congruence
  | [H: _ |- ~ cssaliveout_spec _ _ _ ] =>
      unfold not; intros;
      rewrite orb_false_iff in Eq;
      destruct Eq as [Hr1 Hr2];
      exploit WF; eauto; intros Hr1Lin;
      unfold CSSAlive.Lout in Hr1Lin;
      exploit SSARegSet.mem_1; eauto; intros
  | _ => idtac
  end.
  congruence. congruence.
Qed.

Lemma compute_ninterfere_correct :
  forall f ninterfere r1 r2 d1 d2
         (WFF: wf_cssa_function f),
  cssaval_spec f (compute_cssaval_function f) ->
  compute_ninterfere f (get_all_def f)
    (get_ext_params f (get_all_def f)) = OK ninterfere ->
  ninterfere r1 r2 = true ->
  CSSA.def f r1 d1 ->
  CSSA.def f r2 d2 ->
  ninterfere_spec f r1 r2.
Proof.
  intros.
  unfold compute_ninterfere in H0.
  flatten H0.
  destruct peq.
  + go.
  + simpl in *.
    constructor 2.
    eapply test_ninterlive_correct; eauto.
Qed.

(** ** class interference stuff *)
Lemma check_interference_with_class_correct :
  forall r class ninterf,
  check_interference_with_class r class ninterf = true ->
  forall r',
  In r' class ->
  ninterf r r' = true.
Proof.
  induction class; intros.
  simpl in *. contradiction.
  simpl in *.
  destruct H0.
  rewrite H0 in *.
  rewrite andb_true_iff in H. tauto.
  apply IHclass.
  rewrite andb_true_iff in H. tauto.
  auto.
Qed.

Lemma ninterf_symmetric :
  forall f x y all_defs ninterf,
  compute_ninterfere f all_defs
    (get_ext_params f all_defs) = Errors.OK ninterf ->
  ninterf x y = ninterf y x.
Proof.
  intros.
  unfold compute_ninterfere in H.
  flatten H.
  repeat destruct p2eq;
  repeat destruct peq; simpl; auto; try congruence.
  rewrite orb_comm. auto.
Qed.

Lemma check_interference_in_class_correct :
  forall ninterf class,
  check_interference_in_class class ninterf = true ->
  forall r r',
  In r class ->
  In r' class ->
  r <> r' ->
  (forall x y, ninterf x y = ninterf y x) ->
  ninterf r r' = true.
Proof.
  induction class; intros.
  simpl in *. contradiction.
  simpl in *.
  rewrite andb_true_iff in H.
  destruct H0; destruct H1.
  + congruence.
  + rewrite H0 in *.
    apply check_interference_with_class_correct with (class := class).
    tauto. auto.
  + rewrite H1 in *.
    rewrite H3.
    apply check_interference_with_class_correct with (class := class).
    tauto. auto.
  + apply IHclass; auto.
    tauto.
Qed.

Lemma mem_class_reg_correct_true :
  forall regrepr classes r,
  mem_class_reg regrepr classes r = true ->
  (exists class,
    PTree.get (regrepr r) classes = Some class /\
    In r class) \/
    (r = regrepr r /\ PTree.get (regrepr r) classes = None).
Proof.
  intros.
  case_eq (PTree.get (regrepr r) classes); intros.
  + left.
    exists l.
    unfold mem_class_reg in H.
    flatten H.
    split; auto.
    apply In_reg_correct_true; auto.
  + right.
    unfold mem_class_reg in H.
    flatten H.
    destruct peq; go.
Qed.

Lemma mem_class_regs_correct :
  forall regrepr classes reglist r,
  In r reglist ->
  mem_class_regs regrepr classes reglist = true ->
  (exists class,
    PTree.get (regrepr r) classes = Some class /\
    In r class) \/ 
    (r = regrepr r /\ PTree.get (regrepr r) classes = None).
Proof.
  intros.
  unfold mem_class_regs in H0.
  rewrite forallb_forall in H0.
  specialize (H0 r).
  apply mem_class_reg_correct_true.
  eauto.
Qed.

