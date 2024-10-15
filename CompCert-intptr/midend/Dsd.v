Require Import Classical.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Events.
Require Import Registers.
Require Import Floats.
Require Import Utils.
Require Import Dom.
Require Import SSA. 
Require Import SSAutils. 
Require Import Axioms.
Require Import KildallComp.
Require Import OrderedType.
Require Import Ordered.
Require Import FSets.
Require Import DLib.
Require FSetAVL.
Global Hint Extern 4 (In _ (successors_instr _)) => simpl successors_instr: core.

Unset Allow StrictProp.

(** This file gather other definitions about dominance, related to the
 [dsd] predicate, where [dsd f x pc] holds whenever the definition
 point of register [x] strictly dominates node [pc] *)

Inductive dsd (f:function) (x:reg) (n:node) : Prop :=
| dsd_def_sdom : forall def_x,
    def f x def_x ->
    sdom f def_x n ->
    ~ assigned_phi_spec (fn_phicode f) n x ->
    dsd f x n
| dsd_def_phi :
    assigned_phi_spec (fn_phicode f) n x ->
    dsd f x n.

Lemma ssa_dsd_entry : forall f,
  wf_ssa_function f ->
  forall x,
  dsd f x (fn_entrypoint f) -> 
  False. 
Proof.
  intros. inv H0; auto.
  - inv H1.
    + inv H2. congruence. 
    + inv H2. 
      exploit (@dom_entry node peq); eauto. 
    + inv H2. 
      exploit (@dom_entry node peq); eauto.
  - destruct (fn_entrypoint_inv f); auto.
    inv H0. inv H1. 
    exploit (fn_phicode_code f) ; eauto. intros. destruct H1.
    exploit (fn_phicode_inv1 f) ; eauto.
Qed.  

Lemma dsd_def_params :forall f x n,
  wf_ssa_function f -> 
  reached f n ->
  n <> f.(fn_entrypoint) ->
  ext_params f x ->
  dsd f x n.
Proof.
  intros.
  constructor 1 with (f.(fn_entrypoint)); auto.
  split; auto.
  eapply (@entry_dom node peq); eauto.
  intro Ha.
  inv H2.
  eelim fn_ssa_params; eauto.
  intros _ T; eelim T; eauto. 
  eelim H4; eauto.
Qed.

Lemma dsd_pred_njp : forall f, 
  wf_ssa_function f -> forall n1 n2 x,
  reached f n1 -> n1 <> f.(fn_entrypoint) ->
  cfg f n1 n2 ->
  dsd f x n2 ->
  (dsd f x n1  /\ ~ assigned_phi_spec (fn_phicode f) n2 x) \/
  (def f x n1 /\ ~ assigned_phi_spec (fn_phicode f) n1 x /\ ~ ext_params f x) \/ 
  (assigned_phi_spec (fn_phicode f) n2 x /\ ~ ext_params f x).
Proof.
  intros f H n1 n2 x H0 Hn1 H1 H2. inv H2.
  - (* sdom *)  
    exploit (@sdom_dom_pred node peq) ; go.
    intros Hdom. apply (@dom_eq_sdom node peq) in Hdom. destruct Hdom as [Hdom| Hdom].  
    + (* def_x = n1 *) 
      subst.
      destruct (classic (ext_params f x)) as [E|E].
      * left; split; auto.
        eapply dsd_def_params; eauto.
      * inv H3. 
        right ; left ; repeat split ; auto.
        right ; left ; split ; auto.
        destruct (fn_ssa f) as [HH HH'] ; auto.
        elim (HH x n1 n1) ; eauto. intuition. 
        left ; split ; eauto.
        econstructor 2  ; eauto.
    + (* sdom *)  
      left ; split ; auto.
      econstructor 1 ; eauto.
      intro Hcont. inv Hcont.
      exploit (def_def_eq f x n1 def_x H); eauto.
      intros. inv H7. inv Hdom; intuition.

  - (* assigned phi *)
    right ; right ; split; auto.
    intro. inv H2.
    eelim fn_ssa_params; eauto; intros _ T.
    elim T with n2; auto.
    elim H5 with n2; auto.
Qed. 

Lemma def_dom_sdom_dsd : forall f x pc1 pc2 pc3,
  def f x pc1 ->
  dom f pc1 pc2 ->
  sdom f pc2 pc3 ->
  dsd f x pc3.
Proof.
  intros.
  destruct (classic (assigned_phi_spec (fn_phicode f) pc3 x)).
  constructor 2; auto.
  econstructor 1; eauto.
  eapply (@dom_sdom_trans _ peq); eauto.
Qed.

Lemma def_sdom_dsd : forall f x pc1 pc2,
  def f x pc1 ->
  sdom f pc1 pc2 ->
  dsd f x pc2.
Proof.
  intros.
  eapply def_dom_sdom_dsd; go. 
Qed.

(** Some helful ltac *)
Ltac not_a_def :=
  match goal with
    | [h1: def ?f ?x ?n,
       h2: (fn_code ?f)! ?n = Some _ |- _] =>
      inv h1; [
        idtac
        | match goal with
          | [h3: assigned_code_spec _ ?n ?x |- _] => inv h3; congruence
        end
        | intuition; fail]
  end .

Ltac not_a_phi_def :=
  match goal with
    | [h: assigned_phi_spec _ _ _ |- _] => 
      elim not_jnp_not_assigned_phi_spec with (3:=h); auto; fail
  end.

Ltac simplify_dsd :=
  try not_a_phi_def; try not_a_def;
    try match goal with
          | id1: ext_params ?f ?x, 
            id2: ~ (ext_params ?f ?x) |- _ => elim id2; assumption
        end.

Ltac simp_entry f := 
  exploit (fn_entry f) ; eauto ; intros [ns Hns] ; congruence.

(** More lemmas *)
Lemma dsd_pred_not_join_point : forall f, 
  wf_ssa_function f -> forall n1 n2 x,
  reached f n1 -> 
  cfg f n1 n2 ->
  dsd f x n2 ->
  ~ join_point n2 f -> 
  (ext_params f x /\ n1 = fn_entrypoint f) \/
  (dsd f x n1 /\ ~ assigned_code_spec (fn_code f) n1 x) \/
  (assigned_code_spec (fn_code f) n1 x /\ ~ assigned_phi_spec (fn_phicode f) n1 x).
Proof.
  intros.
  inv H2.
  exploit (sdom_dom_pred peq); eauto; go ; intros Hd.
  destruct (classic (assigned_phi_spec (fn_phicode f) n1 x)).
  right; left; split.
  econstructor 2; eauto.
  intro; eelim unique_def_elim1; eauto.
  eapply fn_ssa; eauto.
  destruct (peq def_x n1).
  inv H4; intuition.
  right; left; split.
  econstructor 1; eauto.
  split; auto.
  intro.
  inv H4.
  inv H8.
  eelim fn_ssa_params; eauto; intros.
  eelim H8; eauto.
  eelim H10; eauto.
  elim n; eapply assigned_code_unique; eauto.
  eelim unique_def_elim1; eauto.
  eapply fn_ssa; eauto.
  eelim not_jnp_not_assigned_phi_spec; eauto.
Qed.

Lemma dsd_pred_jpn' : forall f xk args,
  wf_ssa_function f -> forall
  pc pc' k x phiinstr,
  (fn_code f) ! pc = Some (Inop pc') ->
  index_pred (Kildall.make_predecessors (fn_code f) successors_instr) pc pc' = Some k ->
  In (Iphi args x) phiinstr ->
  (fn_phicode f) ! pc' = Some phiinstr ->
  nth_error args k = Some xk ->
  (dsd f xk pc /\ pc <> fn_entrypoint f) \/ (ext_params f xk /\ pc = fn_entrypoint f).
Proof.
  intros.
  assert (Hu:use f xk pc).
    constructor 2.
    econstructor; eauto.
  eelim ssa_use_exists_def; eauto ; intros def_yk Hdef_yk.
  assert (Hu':dom f def_yk pc) by (eapply ssa_def_dom_use; eauto).
  destruct (classic (assigned_phi_spec (fn_phicode f) pc xk)) as [Hk|Hk].
  left; split.
  constructor 2; auto.  
  intro; subst; eelim no_assigned_phi_spec_fn_entrypoint; eauto.
  elim (dom_eq_sdom peq) with (1:=Hu'); intros Hu''; subst.  
  simplify_dsd; intuition. 
  left; split.
  econstructor ; eauto.
  intro; subst.
  eelim (entry_sdom peq); eauto.  
Qed.

Lemma dsd_pred_jpn : forall xk f,
  wf_ssa_function f -> forall
  pc pc' k args x phiinstr,
  (fn_code f) ! pc = Some (Inop pc') ->
  index_pred (Kildall.make_predecessors (fn_code f) successors_instr) pc pc' = Some k ->
  In (Iphi args x) phiinstr ->
  (fn_phicode f) ! pc' = Some phiinstr ->
  nth_error args k = Some xk ->
  ~ ext_params f xk ->
  dsd f xk pc.
Proof.
  intros.
  assert (Hu:use f xk pc).
    constructor 2.
    econstructor; eauto.
  eelim ssa_use_exists_def; eauto ; intros def_yk Hdef_yk.
  assert (Hu':dom f def_yk pc) by (eapply ssa_def_dom_use; eauto).
  destruct (classic (assigned_phi_spec (fn_phicode f) pc xk)) as [Hk|Hk].
  constructor 2; auto.  
  elim (dom_eq_sdom peq) with (1:=Hu'); intros Hu''; subst.  
  simplify_dsd. 
  econstructor ; eauto.
Qed.

Global Hint Constructors ext_params dsd: core.

Lemma def_match_ins : forall f x pc,
  wf_ssa_function f -> 
  def f x pc ->
  ~ assigned_phi_spec (fn_phicode f) pc x ->
  ~ ext_params f x ->
  match (fn_code f) ! pc with
    | Some (Iop op args dst succ) => dst = x
    | Some (Iload chunk addr args dst succ) => dst = x
    | Some (Icall sig fn args dst succ) => dst = x
    | Some (Ibuiltin fn args (BR dst) succ) => dst = x
    | _ => False
  end.
Proof.
  intros.
  inv H0; try (intuition; fail).
  inv H3; rewrite H0; auto.
Qed.

Lemma dsd_match_ins : forall f x pc,
  wf_ssa_function f -> 
  dsd f x pc ->
  match (fn_code f) ! pc with
    | Some (Iop op args dst succ) => dst <> x
    | Some (Iload chunk addr args dst succ) => dst <> x
    | Some (Icall sig fn args dst succ) => dst <> x
    | Some (Ibuiltin fn args (BR dst) succ) => dst <> x
    | _ => True
  end.
Proof.
  intros.
  case_eq ((fn_code f)!pc); intros; auto.
  destruct i; auto; intros; try intro; subst.
  - assert (assigned_code_spec (fn_code f) pc x).
    econstructor 1; eauto.
    inv H0.
    destruct H4 as [_ H4].
    elim H4; apply ssa_def_unique with f x; auto.
    destruct (fn_ssa _ H) as [T _].
    elim (T x pc pc); intuition.
  - assert (assigned_code_spec (fn_code f) pc x).
    econstructor 2; eauto.
    inv H0.
    destruct H4 as [_ H4].
    elim H4; apply ssa_def_unique with f x; auto.
    destruct (fn_ssa _ H) as [T _].
    elim (T x pc pc); intuition.
  - assert (assigned_code_spec (fn_code f) pc x).
    econstructor 3; eauto.
    inv H0.
    destruct H4 as [_ H4].
    elim H4; apply ssa_def_unique with f x; auto.
    destruct (fn_ssa _ H) as [T _].
    elim (T x pc pc); intuition.
  - destruct b ; auto.
    intro; subst.
    assert (assigned_code_spec (fn_code f) pc x).
    econstructor 4; eauto.
    inv H0.
    destruct H4 as [_ H4].
    elim H4; apply ssa_def_unique with f x; auto.
    destruct (fn_ssa _ H) as [T _].
    elim (T x pc pc); intuition.
Qed.

Lemma dsd_entry_ext_param: forall f x pc,
  wf_ssa_function f ->
  (fn_code f)!(fn_entrypoint f) = Some (Inop pc) ->
  dsd f x pc -> 
  ~ assigned_phi_spec (fn_phicode f) pc x -> 
  ext_params f x.
Proof.
  intros.
  inv H1; intuition.
  exploit (sdom_dom_pred peq); eauto; go.
  intros.
  exploit (dom_entry peq); eauto.
  intros; subst.
  inv H3; auto.
  - inv H6; try congruence. 
  - eelim no_assigned_phi_spec_fn_entrypoint; eauto.
Qed.

Lemma dsd_dom_dsd : forall f x pc1 pc2,
                      dsd f x pc1 -> dom f pc1 pc2 -> dsd f x pc2.
Proof.
  induction 1; intros. 
  - eapply def_dom_sdom_dsd with (pc2:= def_x) ; eauto.
    go.
    eapply (sdom_dom_trans peq); eauto.
  - destruct (peq pc1 pc2).
    + go. 
    + destruct (classic (assigned_phi_spec (fn_phicode f) pc2 x)); go.
Qed.


Lemma wf_ssa_use_phi_dsd : forall f arg pc,
                           forall (WF : wf_ssa_function f)
                                  (REACHED: reached f pc),
                             use_phicode f arg pc ->
                             dsd f arg pc \/ ext_params f arg.
Proof. 
  intros. 
  exploit ssa_use_exists_def; go; intros. invh ex. 
  exploit fn_strict; go. intros Hdom.
  eelim (dom_eq_sdom peq); eauto. 
  - intros. subst. 
    invh def; auto. 
    left. inv H.
    exploit assigned_phi_spec_join_point  ; go. intros.
    exploit pred_is_edge ; eauto. intros EDGE.
    inv EDGE. 
    exploit (fn_code_inv2 f WF pc0 pc); eauto.
    unfold Kildall.successors_list, successors.
    rewrite PTree.gmap1; eauto.
    unfold option_map; rewrite H1; auto.
    invh assigned_code_spec; allinv; congruence.
  - intros.
    left. econstructor; eauto.
    intro Hcont. inv Hcont.
    assert (def f arg pc) by go.
    ssa_def.
    inv H0.
    congruence.
Qed.
