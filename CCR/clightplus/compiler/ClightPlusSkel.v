From compcert Require Import
     AST Maps Globalenvs Memory Values Linking Integers.
From compcert Require Import
     Ctypes Clight.

Require Import CoqlibCCR.
Require Export ZArith.
Require Import String.
Require Import Orders.
Require Export AList.
Require Export Skeleton.

Set Implicit Arguments.

Local Open Scope nat_scope.

Fixpoint _find_idx {A} (f: A -> bool) (l: list A) (acc: nat): option (nat * A) :=
  match l with
  | [] => None
  | hd :: tl => if (f hd) then Some (acc, hd) else _find_idx f tl (S acc)
  end
.

Definition find_idx {A} (f: A -> bool) (l: list A): option (nat * A) := _find_idx f l 0.

Notation "'do' ' X <- A ; B" := (o_bind A (fun _x => match _x with | X => B end))
                                  (at level 200, X pattern, A at level 100, B at level 200)
                                : o_monad_scope.

Lemma find_idx_red {A} (f: A -> bool) (l: list A):
  find_idx f l =
  match l with
  | [] => None
  | hd :: tl =>
    if (f hd)
    then Some (0%nat, hd)
    else
      do (n, a) <- find_idx f tl;
      Some (S n, a)
  end.
Proof.
  unfold find_idx. generalize 0. induction l; ss.
  i. des_ifs; ss.
  - rewrite Heq0. ss.
  - rewrite Heq0. specialize (IHl (S n)). rewrite Heq0 in IHl. ss.
Qed.

Definition gdef := globdef fundef type.

Module GDef <: Typ. Definition t := gdef. End GDef.

Module SkSort := AListSort GDef.

Definition sort: alist gname gdef -> alist gname gdef := SkSort.sort.

Definition incl (sk0 sk1: alist gname gdef): Prop :=
forall gn gd (IN: List.In (gn, gd) sk0),
    List.In (gn, gd) sk1.

Program Definition gdefs: Sk.ld :=
  @Sk.mk (alist gname gdef) nil (@List.app _) sort (fun sk => @List.NoDup _ (List.map fst sk)) (fun sk => ListDec.NoDup_dec string_dec (List.map fst sk)) incl
  _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation.
  econs.
  - ii. ss.
  - ii. eapply H0. eapply H. ss.
Qed.
Next Obligation.
  ii. eapply Permutation.Permutation_in; [|apply IN].
  eapply SkSort.sort_permutation.
Qed.
Next Obligation.
  ii. eapply Permutation.Permutation_in; [|apply IN].
  symmetry. eapply SkSort.sort_permutation.
Qed.
Next Obligation.
  eapply SkSort.sort_add_comm. auto.
Qed.
Next Obligation.
  eapply List.app_assoc.
Qed.
Next Obligation.
  rewrite List.app_nil_r. auto.
Qed.
Next Obligation.
  induction b; ss. red. i. ss. right. et.
Qed.
Next Obligation.
  induction a; ss. red. i. ss. des; subst; et.
Qed.
Next Obligation.
  induction c; ss. red. i. ss. des; subst; et.
Qed.
Next Obligation.
  eapply Permutation.Permutation_NoDup; [|et].
  eapply Permutation.Permutation_map.
  apply Permutation.Permutation_app_comm.
Qed.
Next Obligation.
  eapply Permutation.Permutation_NoDup; [|et].
  eapply Permutation.Permutation_map.
  eapply SkSort.sort_permutation.
Qed.
Next Obligation.
  econs.
Qed.
Next Obligation.
  cut (NoDup (map fst a)).
  { i. eapply Permutation.Permutation_NoDup; [|et].
      eapply Permutation.Permutation_map.
      eapply SkSort.sort_permutation. }
  cut (NoDup (map fst (a ++ b))).
  { i. rewrite map_app in H0.
      eapply nodup_app_l. et. }
  i. eapply Permutation.Permutation_NoDup; [|et].
  eapply Permutation.Permutation_map.
  symmetry. eapply SkSort.sort_permutation.
Qed.

Local Existing Instance gdefs.

Definition load_skenv (sk: Sk.t): (SkEnv.t) :=
  let n := List.length sk in
  {|
      SkEnv.blk2id := fun blk => do '(gn, _) <- (List.nth_error sk blk); Some gn;
      SkEnv.id2blk := fun id => do '(blk, _) <- find_idx (fun '(id', _) => string_dec id id') sk; Some blk
  |}
  .

Lemma load_skenv_wf sk
    (WF: Sk.wf sk)
:
    <<WF: SkEnv.wf (load_skenv sk)>>
.
Proof.
  r in WF.
  rr. split; i; ss.
  - uo; des_ifs.
    + f_equal. ginduction sk; ss. i. inv WF.
      rewrite find_idx_red in Heq1. des_ifs; ss.
      { destruct string_dec in Heq; clarify. }
      des_sumbool. uo. des_ifs. destruct p. ss.
      hexploit IHsk; et.
    + exfalso. ginduction sk; ss. i. inv WF.
      rewrite find_idx_red in Heq2. des_ifs; ss.
      des_sumbool. uo. des_ifs. destruct p. ss.
      hexploit IHsk; et.
  - ginduction sk; ss.
    { i. uo. ss. destruct blk; ss. }
    i. destruct a. inv WF. uo. destruct blk; ss; clarify.
    { rewrite find_idx_red. uo. des_ifs; destruct string_dec in *; ss. }
    hexploit IHsk; et. i.
    rewrite find_idx_red. uo. des_ifs; des_sumbool; ss. exfalso.
    subst. clear - Heq1 H2. ginduction sk; ss. i.
    rewrite find_idx_red in Heq1.
    des_ifs; destruct string_dec; ss; et.
    uo. des_ifs. destruct p. eapply IHsk; et.
Qed.

Definition incl_env (sk0: Sk.t) (skenv: SkEnv.t): Prop :=
  forall gn gd (IN: List.In (gn, gd) sk0),
  exists blk, <<FIND: skenv.(SkEnv.id2blk) gn = Some blk>>.

Lemma incl_incl_env sk0 sk1
    (INCL: incl sk0 sk1)
:
    incl_env sk0 (load_skenv sk1).
Proof.
  ii. exploit INCL; et. i. ss. uo. des_ifs; et.
  exfalso. clear - x0 Heq0. ginduction sk1; et.
  i. ss. rewrite find_idx_red in Heq0. des_ifs.
  des_sumbool. uo.  des_ifs. des; clarify.
  eapply IHsk1; et.
Qed.

Lemma in_env_in_sk :
  forall sk blk symb
        (FIND: SkEnv.blk2id (load_skenv sk) blk = Some symb),
  exists def, In (symb, def) sk.
Proof.
  i. unfold SkEnv.blk2id. ss.
  uo. des_ifs. des; clarify.
  eapply nth_error_In in Heq0. et.
Qed.

Lemma in_sk_in_env :
  forall sk def symb
        (IN: In (symb, def) sk),
  exists blk, SkEnv.blk2id (load_skenv sk) blk = Some symb.
Proof.
  i. unfold SkEnv.blk2id. ss.
  uo. eapply In_nth_error in IN. des.
  eexists. rewrite IN. et.
Qed.

Lemma env_range_some :
  forall sk blk
        (BLKRANGE : blk < Datatypes.length sk),
  <<FOUND : exists symb, SkEnv.blk2id (load_skenv sk) blk = Some symb>>.
Proof.
  i. depgen sk. induction blk; i; ss; clarify.
  - destruct sk; ss; clarify. { lia. }
    uo. destruct p. exists s. ss.
  - destruct sk; ss; clarify. { lia. }
    apply lt_S_n in BLKRANGE. eapply IHblk; eauto.
Qed.

Lemma env_found_range :
  forall sk symb blk
        (FOUND : SkEnv.id2blk (load_skenv sk) symb = Some blk),
  <<BLKRANGE : blk < Datatypes.length sk>>.
Proof.
  induction sk; i; ss; clarify.
  uo; des_ifs. destruct p0. rewrite find_idx_red in Heq0. des_ifs.
  { apply Nat.lt_0_succ. }
  destruct blk.
  { apply Nat.lt_0_succ. }
  uo. des_ifs. destruct p. ss. clarify. apply lt_n_S. eapply IHsk; eauto.
  instantiate (1:=symb). rewrite Heq0. ss.
Qed.

Lemma sk_incl_gd sk0 sk1 gn blk gd:
  Sk.wf sk1 ->
  Sk.le sk0 sk1 ->
  SkEnv.id2blk (load_skenv sk1) gn = Some blk ->
  In (gn, gd) sk0 ->
  nth_error sk1 blk = Some (gn, gd).
Proof.
  ss. i. red in H0. hexploit H0; et. i.
  clear - H3 H1 H. ginduction sk1; i; ss.
  destruct blk; ss.
  - des; clarify. uo. des_ifs. rewrite find_idx_red in Heq0. exfalso.
    des_ifs; des_sumbool; subst.
    + ss. inv H. eapply in_map with (f:=fst) in H3. et.
    + uo. des_ifs.
  - des; clarify. uo. des_ifs. rewrite find_idx_red in Heq0.
    des_ifs; des_sumbool; subst.
    { exfalso. et. }
    eapply IHsk1; et.
    + inv H. et.
    + uo. rewrite find_idx_red in H1. des_ifs.
      uo. unfold curry2 in *. clarify.
Qed.

Global Existing Instance gdefs.
Arguments Sk.unit: simpl never.
Arguments Sk.add: simpl never.
Arguments Sk.wf: simpl never.
Coercion load_skenv: Sk.t >-> SkEnv.t.
Global Opaque load_skenv.