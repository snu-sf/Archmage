Require Import CoqlibCCR.
Require Import ITreelib.
Require Import Skeleton.
Require Import ModSem.
Require Import Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in CoqlibCCR or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import Any.

Set Implicit Arguments.

Local Open Scope nat_scope.










Section SIM.
  Let st_local: Type := (Any.t).

  Variable world: Type.

  Let W: Type := (Any.t) * (Any.t).
  Variable wf: world -> W -> Prop.
  Variable le: relation world.


  Inductive _sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | sim_itree_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          sim_itree _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                 (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itree_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                 (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itree_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_choose_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: exists (x: X), _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itree_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: forall (x: X), _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itree_pput_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      st_src1
      (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itree_pget_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
                 (st_tgt0, i_tgt)


  | sim_itree_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: forall (x: X), _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Choose X) >>= k_tgt)
  | sim_itree_take_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: exists (x: X), _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Take X) >>= k_tgt)

  | sim_itree_pput_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      st_tgt1
      (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)

  | sim_itree_pget_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PGet) >>= k_tgt)

  | sim_itree_progress
      i_src0 i_tgt0 w0 st_src0 st_tgt0 i_src i_tgt
      (SIM: sim_itree _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
      (SRC: i_src0 = true)
      (TGT: i_tgt0 = true)
    :
      _sim_itree sim_itree RR true true w0 (st_src0, i_src) (st_tgt0, i_tgt)
  .

  Definition lift_rel {R_src R_tgt} (w0: world) (RR: R_src -> R_tgt -> Prop)
             (st_src st_tgt: st_local) (ret_src ret_tgt : Any.t) :=
    exists w1 : world,
      (<<WLE: le w0 w1 >> /\ <<WF: wf w1 (st_src, st_tgt) >> /\ <<RET: ret_src = ret_tgt >>).

  Lemma _sim_itree_ind2 (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        (P: bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        (RET: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            v_src v_tgt
            (RET: RR st_src0 st_tgt0 v_src v_tgt),
            P i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt)))
        (CALL: forall
            i_src0 i_tgt0 w w0 st_src0 st_tgt0
            fn varg k_src k_tgt
            (WF: wf w0 (st_src0, st_tgt0))
            (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
                sim_itree _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret)),
            P i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
              (st_tgt0, trigger (Call fn varg) >>= k_tgt))
        (SYSCALL: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            fn varg rvs k_src k_tgt
            (K: forall vret,
                sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
              (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt))
        (TAUSRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt))
        (CHOOSESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: exists (x: X), <<SIM: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
              (st_tgt0, i_tgt))
        (TAKESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: forall (x: X), <<SIM: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
              (st_tgt0, i_tgt))
        (PPUTSRC: forall
            i_src0 i_tgt0 w0 st_tgt0 st_src0
            k_src i_tgt
            st_src1
            (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
              (st_tgt0, i_tgt))
        (PGETSRC: forall
            i_src0 i_tgt0 w0 st_tgt0 st_src0
            k_src i_tgt
            (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
              (st_tgt0, i_tgt))
        (TAUTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt))
        (CHOOSETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: forall (x: X), <<SIMH: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Choose X) >>= k_tgt))
        (TAKETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: exists (x: X), <<SIM:_sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Take X) >>= k_tgt))
        (PPUTTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt i_src
            st_tgt1
            (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt))
        (PGETTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt i_src
            (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0)),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (PGet) >>= k_tgt))
        (PROGRESS: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0 i_src i_tgt
            (SIM: sim_itree _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (SRC: i_src0 = true)
            (TGT: i_tgt0 = true),
            P true true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      forall i_src0 i_tgt0 w0 st_src st_tgt
             (SIM: _sim_itree sim_itree RR i_src0 i_tgt0 w0 st_src st_tgt),
        P i_src0 i_tgt0 w0 st_src st_tgt.
  Proof.
    fix IH 6. i. inv SIM.
    { eapply RET; eauto. }
    { eapply CALL; eauto. }
    { eapply SYSCALL; eauto. }
    { eapply TAUSRC; eauto. }
    { eapply CHOOSESRC; eauto. des. esplits; eauto. }
    { eapply TAKESRC; eauto. }
    { eapply PPUTSRC; eauto. }
    { eapply PGETSRC; eauto. }
    { eapply TAUTGT; eauto. }
    { eapply CHOOSETGT; eauto. }
    { eapply TAKETGT; eauto. des. esplits; eauto. }
    { eapply PPUTTGT; eauto. }
    { eapply PGETTGT; eauto. }
    { eapply PROGRESS; eauto. }
  Qed.

  Definition sim_itree o_src o_tgt w0: relation _ :=
    paco8 _sim_itree bot8 _ _ (lift_rel w0 (@eq Any.t)) o_src o_tgt w0.

  Lemma sim_itree_mon: monotone8 _sim_itree.
  Proof.
    ii. induction IN using _sim_itree_ind2; try (by des; econs; ss; et).
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree_mon: paco.
  Hint Resolve cpn8_wcompat: paco.

  Lemma sim_itree_ind
        R_src R_tgt (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        (P: bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        (RET: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            v_src v_tgt
            (RET: RR st_src0 st_tgt0 v_src v_tgt),
            P i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt)))
        (CALL: forall
            i_src0 i_tgt0 w w0 st_src0 st_tgt0
            fn varg k_src k_tgt
            (WF: wf w0 (st_src0, st_tgt0))
            (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
                paco8 _sim_itree bot8 _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret)),
            P i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
              (st_tgt0, trigger (Call fn varg) >>= k_tgt))
        (SYSCALL: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            fn varg rvs k_src k_tgt
            (K: forall vret,
                paco8 _sim_itree bot8 _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
              (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt))
        (TAUSRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt))
        (CHOOSESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: exists (x: X), <<SIM: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
              (st_tgt0, i_tgt))
        (TAKESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: forall (x: X), <<SIM: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
              (st_tgt0, i_tgt))
        (PPUTSRC: forall
            i_src0 i_tgt0 w0 st_tgt0 st_src0
            k_src i_tgt
            st_src1
            (K: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
              (st_tgt0, i_tgt))
        (PGETSRC: forall
            i_src0 i_tgt0 w0 st_tgt0 st_src0
            k_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
              (st_tgt0, i_tgt))
        (TAUTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt))
        (CHOOSETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: forall (x: X), <<SIMH: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Choose X) >>= k_tgt))
        (TAKETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: exists (x: X), <<SIM:paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Take X) >>= k_tgt))
        (PPUTTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt i_src
            st_tgt1
            (K: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt))
        (PGETTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt i_src
            (K: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0)),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (PGet) >>= k_tgt))
        (PROGRESS: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0 i_src i_tgt
            (SIM: paco8 _sim_itree bot8 _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (SRC: i_src0 = true)
            (TGT: i_tgt0 = true),
            P true true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      forall i_src0 i_tgt0 w0 st_src st_tgt
             (SIM: paco8 _sim_itree bot8 _ _ RR i_src0 i_tgt0 w0 st_src st_tgt),
        P i_src0 i_tgt0 w0 st_src st_tgt.
  Proof.
    i. punfold SIM. induction SIM using _sim_itree_ind2.
    { eapply RET; eauto. }
    { eapply CALL; eauto. i. exploit K; eauto. i. pclearbot. eauto. }
    { eapply SYSCALL; eauto. i. exploit K; eauto. i. pclearbot. eauto. }
    { eapply TAUSRC; eauto. }
    { eapply CHOOSESRC; eauto. des. esplits; eauto. }
    { eapply TAKESRC; eauto. i. exploit K; eauto. i. des.
      pclearbot. esplits; eauto. }
    { eapply PPUTSRC; eauto. }
    { eapply PGETSRC; eauto. }
    { eapply TAUTGT; eauto. }
    { eapply CHOOSETGT; eauto. i. exploit K; eauto. i. des.
      pclearbot. esplits; eauto. }
    { eapply TAKETGT; eauto. des. esplits; eauto. }
    { eapply PPUTTGT; eauto. }
    { eapply PGETTGT; eauto. }
    { eapply PROGRESS; eauto. pclearbot. auto. }
  Qed.

  Variant sim_itree_indC (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_indC_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | sim_itree_indC_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          sim_itree _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                     (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itree_indC_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                     (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itree_indC_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: sim_itree _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_indC_choose_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: exists (x: X), sim_itree _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                     (st_tgt0, i_tgt)
  | sim_itree_indC_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: forall (x: X), sim_itree _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                     (st_tgt0, i_tgt)

  | sim_itree_indC_pput_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      st_src1
      (K: sim_itree _ _ RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
                     (st_tgt0, i_tgt)

  | sim_itree_indC_pget_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      (K: sim_itree _ _ RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
                     (st_tgt0, i_tgt)


  | sim_itree_indC_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_indC_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: forall (x: X), sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (Choose X) >>= k_tgt)
  | sim_itree_indC_take_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: exists (x: X), sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (Take X) >>= k_tgt)

  | sim_itree_indC_pput_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      st_tgt1
      (K: sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)

  | sim_itree_indC_pget_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      (K: sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (PGet) >>= k_tgt)
  .

  Lemma sim_itree_indC_mon: monotone8 sim_itree_indC.
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
  Qed.
  Hint Resolve sim_itree_indC_mon: paco.

  Lemma sim_itree_indC_spec:
    sim_itree_indC <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. i. exploit K; eauto. i. des.
      esplits; eauto. eapply rclo8_base. eauto. }
    { econs 3; eauto. i. eapply rclo8_base. eauto. }
    { econs 4; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 5; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 6; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 7; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 8; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 9; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 10; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 11; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 12; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 13; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
  Qed.

  Variant sim_itreeC (r g: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itreeC_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | sim_itreeC_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          g _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                 (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itreeC_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          g _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                 (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itreeC_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: r _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itreeC_choose_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: exists (x: X), r _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itreeC_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: forall (x: X), r _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itreeC_pput_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      st_src1
      (K: r _ _ RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itreeC_pget_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      (K: r _ _ RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
                 (st_tgt0, i_tgt)


  | sim_itreeC_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itreeC_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: forall (x: X), r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Choose X) >>= k_tgt)
  | sim_itreeC_take_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: exists (x: X), r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Take X) >>= k_tgt)

  | sim_itreeC_pput_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      st_tgt1
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)

  | sim_itreeC_pget_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PGet) >>= k_tgt)
  .

  Lemma sim_itreeC_spec_aux:
    sim_itreeC <10= gpaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    i. inv PR.
    { gstep. econs 1; eauto. }
    { gstep. econs 2; eauto. i. gbase. eauto. }
    { gstep. econs 3; eauto. i. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 4; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 5; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 6; eauto. i. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 7; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 8; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 9; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 10; eauto. i. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 11; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 12; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 13; eauto. gbase. eauto. }
  Qed.

  Lemma sim_itreeC_spec r g
    :
      @sim_itreeC (gpaco8 (_sim_itree) (cpn8 _sim_itree) r g) (gpaco8 (_sim_itree) (cpn8 _sim_itree) g g)
      <8=
      gpaco8 (_sim_itree) (cpn8 _sim_itree) r g.
  Proof.
    i. eapply gpaco8_gpaco; [eauto with paco|].
    eapply gpaco8_mon.
    { eapply sim_itreeC_spec_aux. eauto. }
    { auto. }
    { i. eapply gupaco8_mon; eauto. }
  Qed.

  Lemma sim_itree_progress_flag R0 R1 RR r g w st_src st_tgt
        (SIM: gpaco8 _sim_itree (cpn8 _sim_itree) g g R0 R1 RR false false w st_src st_tgt)
    :
      gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR true true w st_src st_tgt.
  Proof.
    gstep. destruct st_src, st_tgt. econs; eauto.
  Qed.

  Lemma sim_itree_flag_mon
        (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        R_src R_tgt (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        f_src0 f_tgt0 f_src1 f_tgt1 w st_src st_tgt
        (SIM: @_sim_itree sim_itree _ _ RR f_src0 f_tgt0 w st_src st_tgt)
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      @_sim_itree sim_itree _ _ RR f_src1 f_tgt1 w st_src st_tgt.
  Proof.
    revert f_src1 f_tgt1 SRC TGT.
    induction SIM using _sim_itree_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. des. esplits; eauto. }
    { econs 6; eauto. i. exploit K; eauto. i. des. eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. i. exploit K; eauto. i. des. eauto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { exploit SRC0; auto. exploit TGT0; auto. i. clarify. econs 14; eauto. }
  Qed.

  Definition sim_fsem: relation (option mname * Any.t -> itree Es Any.t) :=
    (eq ==> (fun it_src it_tgt => forall w mrs_src mrs_tgt (SIMMRS: wf w (mrs_src, mrs_tgt)),
                 sim_itree false false w (mrs_src, it_src)
                           (mrs_tgt, it_tgt)))%signature
  .

  Definition sim_fnsem: relation (string * (option mname * Any.t -> itree Es Any.t)) := RelProd eq sim_fsem.


  Variant lflagC (r: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | lflagC_intro
      f_src0 f_src1 f_tgt0 f_tgt1 w st_src st_tgt
      (SIM: r _ _ RR f_src0 f_tgt0 w st_src st_tgt)
      (SRC: f_src0 = true -> f_src1 = true)
      (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      lflagC r RR f_src1 f_tgt1 w st_src st_tgt
  .

  Lemma lflagC_mon
        r1 r2
        (LE: r1 <8= r2)
    :
      @lflagC r1 <8= @lflagC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve lflagC_mon: paco.

  Lemma lflagC_spec: lflagC <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eapply GF in SIM.
    revert x3 x4 SRC TGT. induction SIM using _sim_itree_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. i. exploit K; eauto. i. des.
      esplits; eauto. eapply rclo8_base. eauto. }
    { econs 3; eauto. i. eapply rclo8_base. eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. des. esplits; eauto. }
    { econs 6; eauto. i. exploit K; eauto. i. des. esplits; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. i. exploit K; eauto. i. des. esplits; eauto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { exploit SRC0; auto. exploit TGT0; auto. i. clarify. econs 14; eauto.
      eapply rclo8_base; auto. }
  Qed.

  Lemma sim_itree_flag_down R0 R1 RR r g w st_src st_tgt f_src f_tgt
        (SIM: gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR false false w st_src st_tgt)
    :
      gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR f_src f_tgt w st_src st_tgt.
  Proof.
    guclo lflagC_spec. econs; eauto.
  Qed.

  Lemma sim_itree_bot_flag_up R0 R1 RR w st_src st_tgt f_src f_tgt
        (SIM: paco8 _sim_itree bot8 R0 R1 RR true true w st_src st_tgt)
    :
      paco8 _sim_itree bot8 R0 R1 RR f_src f_tgt w st_src st_tgt.
  Proof.
    ginit. remember true in SIM at 1. remember true in SIM at 1.
    clear Heqb Heqb0. revert w st_src st_tgt f_src f_tgt b b0 SIM.
    gcofix CIH. i. revert f_src f_tgt.

    (* TODO: why induction using sim_itree_ind doesn't work? *)
    pattern b, b0, w, st_src, st_tgt.
    match goal with
    | |- ?P b b0 w st_src st_tgt => set P
    end.
    revert b b0 w st_src st_tgt SIM.
    eapply (@sim_itree_ind R0 R1 RR P); subst P; ss; i; clarify.
    { guclo sim_itree_indC_spec. econs 1; eauto. }
    { gstep. econs 2; eauto. i. gbase. eapply CIH; eauto. }
    { gstep. econs 3; eauto. i. gbase. eapply CIH; eauto. }
    { guclo sim_itree_indC_spec. econs 4; eauto. }
    { guclo sim_itree_indC_spec. econs 5; eauto. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 6; eauto. i. hexploit K; eauto. i. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 7; eauto. }
    { guclo sim_itree_indC_spec. econs 8; eauto. }
    { guclo sim_itree_indC_spec. econs 9; eauto. }
    { guclo sim_itree_indC_spec. econs 10; eauto. i. hexploit K; eauto. i. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 11; eauto. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 12; eauto. }
    { guclo sim_itree_indC_spec. econs 13; eauto. }
    { eapply sim_itree_flag_down. gfinal. right.
      eapply paco8_mon; eauto. ss.
    }
  Qed.

  Variant lbindR (r s: forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), bool -> bool -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop):
    forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), bool -> bool -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop :=
  | lbindR_intro
      f_src f_tgt w0 w1

      R_src R_tgt RR
      (st_src0 st_tgt0: st_local)
      (i_src: itree Es R_src) (i_tgt: itree Es R_tgt)
      (SIM: r _ _ RR f_src f_tgt w0 (st_src0, i_src) (st_tgt0, i_tgt))

      S_src S_tgt SS
      (k_src: ktree Es R_src S_src) (k_tgt: ktree Es R_tgt S_tgt)
      (SIMK: forall st_src1 st_tgt1 vret_src vret_tgt (SIM: RR st_src1 st_tgt1 vret_src vret_tgt), s _ _ SS false false w1 (st_src1, k_src vret_src) (st_tgt1, k_tgt vret_tgt))
    :
      lbindR r s SS f_src f_tgt w1 (st_src0, ITree.bind i_src k_src) (st_tgt0, ITree.bind i_tgt k_tgt)
  .

  Hint Constructors lbindR: core.

  Lemma lbindR_mon
        r1 r2 s1 s2
        (LEr: r1 <8= r2) (LEs: s1 <8= s2)
    :
      lbindR r1 s1 <8= lbindR r2 s2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Definition lbindC r := lbindR r r.
  Hint Unfold lbindC: core.

  Lemma lbindC_wrespectful: wrespectful8 (_sim_itree) lbindC.
  Proof.
    econs.
    { ii. eapply lbindR_mon; eauto. }
    i. rename l into llll. inv PR; csc.
    remember (st_src0, i_src). remember(st_tgt0, i_tgt).
    revert st_src0 i_src st_tgt0 i_tgt Heqp Heqp0.
    revert k_src k_tgt SIMK. eapply GF in SIM.
    induction SIM using _sim_itree_ind2; i; clarify.
    + rewrite ! bind_ret_l. exploit SIMK; eauto. i.
      eapply sim_itree_flag_mon.
      { eapply sim_itree_mon; eauto. i. eapply rclo8_base. auto. }
      { ss. }
      { ss. }
    + rewrite ! bind_bind. econs; eauto. i.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. i.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto. i. exploit K; eauto. i. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. i. exploit K; eauto. i. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
    + econs; eauto. eapply rclo8_clo_base. econs; eauto.
  Qed.

  Lemma lbindC_spec: lbindC <9= gupaco8 (_sim_itree) (cpn8 (_sim_itree)).
  Proof.
    intros. eapply wrespect8_uclo; eauto with paco. eapply lbindC_wrespectful.
  Qed.

End SIM.
Hint Resolve sim_itree_mon: paco.
Hint Resolve cpn8_wcompat: paco.

Lemma self_sim_itree:
  forall st itr,
    sim_itree (fun _ '(src, tgt) => src = tgt) top2 false false tt (st, itr) (st, itr).
Proof.
  ginit. gcofix CIH. i. ides itr.
  { gstep. eapply sim_itree_ret; ss. }
  { guclo sim_itree_indC_spec. econs.
    guclo sim_itree_indC_spec. econs.
    eapply sim_itree_progress_flag. gbase. auto.
  }
  destruct e.
  { dependent destruction c. rewrite <- ! bind_trigger. gstep.
    eapply sim_itree_call; ss. ii. subst.
    eapply sim_itree_flag_down. gbase. auto.
  }
  destruct s.
  { rewrite <- ! bind_trigger. resub. dependent destruction p.
    { guclo sim_itree_indC_spec. econs.
      guclo sim_itree_indC_spec. econs.
      eapply sim_itree_progress_flag. gbase. auto.
    }
    { guclo sim_itree_indC_spec. econs.
      guclo sim_itree_indC_spec. econs.
      eapply sim_itree_progress_flag. gbase. auto.
    }
  }
  { rewrite <- ! bind_trigger. resub. dependent destruction e.
    { guclo sim_itree_indC_spec. econs 10. i.
      guclo sim_itree_indC_spec. econs. eexists.
      eapply sim_itree_progress_flag. gbase. eauto.
    }
    { guclo sim_itree_indC_spec. econs 6. i.
      guclo sim_itree_indC_spec. econs. eexists.
      eapply sim_itree_progress_flag. gbase. eauto.
    }
    { guclo sim_itree_indC_spec. econs. i.
      eapply sim_itree_progress_flag. gbase. auto.
    }
  }
Qed.



(*** desiderata: (1) state-aware simulation relation !!!! ***)
(*** (2) not whole function frame, just my function frame !!!! ***)
(*** (3) would be great if induction tactic works !!!! (study itree case study more) ***)



Module ModSemPair.
Section SIMMODSEM.

  Variable (ms_src ms_tgt: ModSem.t).

  Let W: Type := (Any.t) * (Any.t).
  Inductive sim: Prop := mk {
    world: Type;
    wf: world -> W -> Prop;
    le: world -> world -> Prop;
    le_PreOrder: PreOrder le;
    sim_fnsems: Forall2 (sim_fnsem wf le) ms_src.(ModSem.fnsems) ms_tgt.(ModSem.fnsems);
    sim_mn: ms_src.(ModSem.mn) = ms_tgt.(ModSem.mn);
    sim_initial: exists w_init, wf w_init (ms_src.(ModSem.initial_st), ms_tgt.(ModSem.initial_st));
  }.

End SIMMODSEM.

Lemma self_sim (ms: ModSem.t):
  sim ms ms.
Proof.
  econs; et.
  - instantiate (1:=fun (_ _: unit) => True). ss.
  - instantiate (1:=(fun (_: unit) '(src, tgt) => src = tgt)). (* fun p => fst p = snd p *)
    generalize (ModSem.fnsems ms).
    induction l; ii; ss.
    econs; eauto. econs; ss. ii; clarify.
    destruct w. exploit self_sim_itree; et.
  - ss.
Unshelve.
all: try (exact 0).
Qed.

End ModSemPair.








Module ModLPair.
Section SIMMOD.
  Context `{Sk.ld}.
  Variable (mds_src mds_tgt: list Mod.t).

  Inductive sim sk: Prop := mk {
     sim_modsem:
        forall (SKINCL: Forall (flip Sk.le sk) (List.map Mod.sk mds_tgt))
              (SKWF: Sk.wf sk),
         <<SIM: Forall2 ModSemPair.sim (List.map (flip Mod.get_modsem sk) mds_src) (List.map (flip Mod.get_modsem sk) mds_tgt)>>;
     sim_sk: <<SIM: Forall2 eq (List.map Mod.sk mds_src) (List.map Mod.sk mds_tgt)>>;
   }.

End SIMMOD.

Section CONFIRM.
  Context `{Sk.ld}.

  Lemma sim_app mds_src1 mds_src2 mds_tgt1 mds_tgt2 sk
        (SIM1: sim mds_src1 mds_tgt1 sk) 
        (SIM2: sim mds_src2 mds_tgt2 sk)
    :
        <<SIM_TOTAL: sim (mds_src1 ++ mds_src2) (mds_tgt1 ++ mds_tgt2) sk>>.
  Proof.
    inv SIM1. inv SIM2. econs; cycle 1.
    { do 2 rewrite map_app. apply Forall2_app; et. }
    i. red. do 2 rewrite map_app. rewrite map_app in SKINCL.
    rewrite List.Forall_app in SKINCL. des.
    apply Forall2_app; tauto.
  Qed.

End CONFIRM.

End ModLPair.


Module ModPair.
Section SIMMOD.
  Context `{Sk.ld}.
   Variable (md_src md_tgt: Mod.t).
   Inductive sim: Prop := mk {
     sim_modsem:
       forall sk
              (SKINCL: Sk.le md_tgt.(Mod.sk) sk)
              (SKWF: Sk.wf sk),
         <<SIM: ModSemPair.sim (md_src.(Mod.get_modsem) sk) (md_tgt.(Mod.get_modsem) sk)>>;
     sim_sk: <<SIM: md_src.(Mod.sk) = md_tgt.(Mod.sk)>>;
   }.

End SIMMOD.

End ModPair.


Section SIMMOD.

  Context {CONF: EMSConfig}.
  Context `{Sk.ld}.

  Lemma ModL_add_fnsems md0 md1 sk
    :
      (ModSemL.fnsems (ModL.get_modsem (ModL.add md0 md1) sk)) =
      (ModSemL.fnsems (ModL.get_modsem md0 sk)) ++ (ModSemL.fnsems (ModL.get_modsem md1 sk)).
  Proof.
    ss.
  Qed.

  Lemma ModL_add_sk md0 md1
    :
      ModL.sk (ModL.add md0 md1) = Sk.add (ModL.sk md0) (ModL.sk md1).
  Proof.
    ss.
  Qed.

  Lemma Mod_list_incl_sk (mds: list Mod.t) md
        (IN: In md mds)
    :
      Sk.le (Mod.sk md) (ModL.sk (Mod.add_list mds)).
  Proof.
    rewrite Mod.add_list_sk. revert IN. induction mds; ss.
    i. des; clarify.
    { ii. eapply Sk.le_add_r. }
    { ii. etrans. apply IHmds; et. apply Sk.le_add_l. }
  Qed.

  Lemma Mod_add_list_get_modsem (mds: list Mod.t) sk
    :
      ModL.get_modsem (Mod.add_list mds) sk
      =
      fold_right ModSemL.add {| ModSemL.fnsems := []; ModSemL.initial_mrs := [] |}
                 (List.map (fun (md: Mod.t) => ModL.get_modsem md sk) mds).
  Proof.
    induction mds; ss. f_equal. rewrite <- IHmds. ss.
  Qed.

End SIMMOD.


Require Import SimGlobal.
Require Import Red IRed.

Module TAC.
  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac step := ired_both; guclo simg_safe_spec; econs; et; i.
  Ltac steps := (repeat step); ired_both.

  Ltac force := ired_both; guclo simg_indC_spec; econs; et.
End TAC.
Import TAC.

Section ADEQUACY.
  Section SEMPAIR.
    Variable ms_src: ModSemL.t.
    Variable ms_tgt: ModSemL.t.

    Variable mn: mname.
    Variable world: Type.
    Variable wf: world -> Any.t * Any.t -> Prop.
    Variable le: world -> world -> Prop.

    Hypothesis le_PreOrder: PreOrder le.

    Hypothesis fnsems_find_iff:
      forall fn,
        (<<NONE: alist_find fn ms_src.(ModSemL.fnsems) = None>>) \/
        (exists mn' (f: _ -> itree _ _),
            (<<MN: mn <> mn'>>) /\
            (<<SRC: alist_find fn ms_src.(ModSemL.fnsems) = Some (transl_all mn' (T:=Any.t) ∘ f)>>) /\
            (<<TGT: alist_find fn ms_tgt.(ModSemL.fnsems) = Some (transl_all mn' (T:=Any.t) ∘ f)>>)) \/
        (exists (f_src f_tgt: _ -> itree _ _),
            (<<SRC: alist_find fn ms_src.(ModSemL.fnsems) = Some (transl_all mn (T:=Any.t) ∘ f_src)>>) /\
            (<<TGT: alist_find fn ms_tgt.(ModSemL.fnsems) = Some (transl_all mn (T:=Any.t) ∘ f_tgt)>>) /\
            (<<SIM: sim_fsem wf le f_src f_tgt>>)).


    Variant g_lift_rel
            (w0: world) (st_src st_tgt: p_state): Prop :=
    | g_lift_rel_intro
        w1
        (LE: le w0 w1)
        (MN: wf w1 (st_src mn, st_tgt mn))
        (NMN: forall mn' (NIN: mn <> mn'), st_src mn' = st_tgt mn')
    .

    Variant my_r0:
      forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop :=
    | my_r0_intro
        w0
        (itr_src itr_tgt: itree Es Any.t)
        st_src st_tgt o_src o_tgt
        (SIM: sim_itree wf le o_src o_tgt w0 (st_src mn, itr_src) (st_tgt mn, itr_tgt))
        (STATE: forall mn' (MN: mn <> mn'), st_src mn' = st_tgt mn')
      :
        my_r0 (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
                 g_lift_rel w0 st_src st_tgt /\ ret_src = ret_tgt)
              o_src o_tgt
              (EventsL.interp_Es (ModSemL.prog ms_src) (transl_all mn itr_src) st_src)
              (EventsL.interp_Es (ModSemL.prog ms_tgt) (transl_all mn itr_tgt) st_tgt)
    .

    Variant my_r1:
      forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop :=
    | my_r1_intro
        mn' w0 st_src st_tgt
        (MN: mn <> mn')
        (SIM: g_lift_rel w0 st_src st_tgt)
        (itr: itree Es Any.t)
      :
        my_r1 (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
                 g_lift_rel w0 st_src st_tgt /\ ret_src = ret_tgt)
              false false
              (EventsL.interp_Es (ModSemL.prog ms_src) (transl_all mn' itr) st_src)
              (EventsL.interp_Es (ModSemL.prog ms_tgt) (transl_all mn' itr) st_tgt)
    .

    Let my_r := my_r0 \7/ my_r1.
    Let sim_lift: my_r <7= simg.
    Proof.
      ginit.
      { i. eapply cpn7_wcompat; eauto with paco. }
      gcofix CIH. i. destruct PR.
      { destruct H.
        unfold sim_itree in SIM.
        remember (st_src mn, itr_src).
        remember (st_tgt mn, itr_tgt).
        remember w0 in SIM at 2.
        revert st_src itr_src st_tgt itr_tgt Heqp Heqp0 Heqw STATE.

        (* TODO: why induction using sim_itree_ind doesn't work? *)
        pattern o_src, o_tgt, w, p, p0.
        match goal with
        | |- ?P o_src o_tgt w p p0 => set P
        end.
        revert o_src o_tgt w p p0 SIM.
        eapply (@sim_itree_ind world wf le Any.t Any.t (lift_rel wf le w0 (@eq Any.t)) P); subst P; ss; i; clarify.

        - rr in RET. des. step. splits; auto. econs; et.
        - hexploit (fnsems_find_iff fn). i. des.
          { steps. rewrite NONE. unfold unwrapU, triggerUB. step. ss. }
          { steps. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
            apply simg_progress_flag.
            guclo bindC_spec. econs.
            { gbase. eapply CIH. right. econs; ss. econs; et. refl. }
            { i. ss. des. destruct vret_src, vret_tgt. des; clarify. inv SIM.
              hexploit K; et. i. des. pclearbot.
              steps. gbase. eapply CIH. left. econs; et.
            }
          }
          { hexploit (SIM (Some mn, varg) (Some mn, varg)); et. i. des.
            steps. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
            apply simg_progress_flag.
            guclo bindC_spec. econs.
            { gbase. eapply CIH. left. econs; ss. et. }
            { i. ss. destruct vret_src, vret_tgt. des; clarify. inv SIM0.
              hexploit K; et. i. des. pclearbot.
              steps. gbase. eapply CIH. left. econs; et.
            }
          }
        - step. i. subst. apply simg_progress_flag.
          hexploit (K x_tgt). i. des. pclearbot.
          steps. gbase. eapply CIH. left. econs; et.
        - ired_both. steps.
        - des. force. exists x. steps. eapply IH; eauto.
        - steps. i. hexploit K. i. des. steps. eapply IH; eauto.
        - steps. eapply IH; eauto.
          { unfold update. des_ifs. }
          { i. unfold update. des_ifs. et. }
        - steps. eapply IH; eauto.
        - steps.
        - steps. i. hexploit K. i. des. steps. eapply IH; eauto.
        - des. force. exists x. steps. eapply IH; eauto.
        - steps. eapply IH; eauto.
          { unfold update. des_ifs. }
          { i. unfold update. des_ifs. et. }
        - steps. eapply IH; eauto.
        - eapply simg_progress_flag. gbase. eapply CIH.
          left. econs; eauto.
      }
      { destruct H. ides itr.
        { steps. }
        { steps. eapply simg_progress_flag. gbase. eapply CIH. right. econs; et. }
        rewrite <- ! bind_trigger. destruct e.
        { resub. destruct c. hexploit (fnsems_find_iff fn). i. des.
          { steps. rewrite NONE. unfold unwrapU, triggerUB. step. ss. }
          { inv SIM. steps. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
            guclo bindC_spec. econs.
            { eapply simg_progress_flag. gbase. eapply CIH.
              right. econs; ss. econs; et. }
            { i. ss. des. destruct vret_src, vret_tgt. des; clarify.
              steps. eapply simg_progress_flag.
              gbase. eapply CIH. right. econs; et. }
          }
          { inv SIM. hexploit (SIM0 (Some mn', args) (Some mn', args)); et. i. des.
            steps. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
            guclo bindC_spec. econs.
            { eapply simg_progress_flag. gbase. eapply CIH. left. econs; ss. et. }
            { i. ss. destruct vret_src, vret_tgt. des; clarify.
              steps. eapply simg_progress_flag. gbase. eapply CIH. right. econs; et.
              inv SIM. econs.
              { etrans; et. }
              { et. }
              { et. }
            }
          }
        }
        destruct s.
        { resub. destruct p.
          { steps. eapply simg_progress_flag.
            gbase. eapply CIH. right. econs; et.
            inv SIM. econs; et.
            { unfold update. des_ifs. }
            { ii. unfold update. des_ifs. et. }
          }
          { steps. eapply simg_progress_flag.
            gbase. eapply CIH. right.
            replace (st_tgt mn') with (st_src mn'); et.
            { econs; et. }
            { inv SIM. et. }
          }
        }
        { resub. destruct e.
          { steps. force. exists x. steps. eapply simg_progress_flag.
            gbase. eapply CIH; et. right. econs; et.
          }
          { steps. force. exists x. steps. eapply simg_progress_flag.
            gbase. eapply CIH; et. right. econs; et.
          }
          { steps. subst. eapply simg_progress_flag.
            gbase. eapply CIH; et. right. econs; et. }
        }
      }
    Qed.

    Context `{CONF: EMSConfig}.

    Hypothesis INIT:
      exists w, g_lift_rel w (ModSemL.initial_p_state ms_src) (ModSemL.initial_p_state ms_tgt).

    Lemma adequacy_local_aux (P Q: bool)
          (WF: Q = true -> P = true)
      :
        (Beh.of_program (ModSemL.compile ms_tgt (Some P)))
        <1=
        (Beh.of_program (ModSemL.compile ms_src (Some Q))).
    Proof.
      eapply adequacy_global_itree; ss.
      hexploit INIT. i. des. ginit.
      { eapply cpn7_wcompat; eauto with paco. }
      unfold ModSemL.initial_itr, assume.
      hexploit (fnsems_find_iff "main"). i. des.
      { unfold triggerUB. destruct Q; steps; ss. unshelve esplits; et. unfold ITree.map, unwrapU, triggerUB. steps.
        rewrite NONE. steps. ss. }
      { unfold triggerUB. destruct Q; steps; ss. unshelve esplits; et. unfold ITree.map, unwrapU. steps.
        rewrite SRC. rewrite TGT.
        steps. rewrite WF; et. steps.
        guclo bindC_spec. econs.
        { gfinal. right. eapply sim_lift. right. econs; et. }
        { i. destruct vret_src, vret_tgt. des; clarify. steps. }
      }
      { inv H. hexploit (SIM (None, initial_arg) (None, initial_arg)); et. i. des.
        unfold triggerUB. destruct Q; steps; ss. 
        rewrite WF; et.
        steps. unfold ITree.map, unwrapU. steps.
        rewrite SRC. rewrite TGT. steps. guclo bindC_spec. econs.
        { eapply simg_flag_down. gfinal. right. eapply sim_lift. left. econs; et. }
        { i. destruct vret_src, vret_tgt. des; clarify. steps. }
      }
      Unshelve. all: try exact 0.
    Qed.
  End SEMPAIR.

  Context `{Sk.ld}.

  Theorem adequacy_local_strong_l mds_src mds_tgt
          (SIM: forall sk, ModLPair.sim mds_src mds_tgt sk)
    :
      <<CR: (refines_strong (Mod.add_list mds_tgt) (Mod.add_list mds_src))>>
  .
  Proof.
    ii. unfold ModL.compile, ModL.enclose, ModL.wf_bool in *.
    set (ModL.wf_dec _) as wf_src. set (ModL.wf_dec _) as wf_tgt in PR.
    set (ModL.sk _) as sk_src. set (ModL.sk _) as sk_tgt in PR.
    specialize (SIM (Sk.canon sk_tgt)). inv SIM.
    destruct wf_src; cycle 1.
    { eapply ModSemL.compile_not_wf; et. }
    ss. rename w into SKWF.
    assert (SKEQ: sk_src = sk_tgt).
    { unfold sk_src, sk_tgt. ss. f_equal. clear -sim_sk.
      ginduction mds_src; i.
      - inv sim_sk. destruct mds_tgt; clarify.
      - destruct mds_tgt; inv sim_sk. ss. f_equal; et. }
    hexploit sim_modsem; et.
    { clear. unfold sk_tgt. clear sk_tgt.
      ss. set (ModL.sk (Mod.add_list ctx)) as sk_ctx.
      clearbody sk_ctx. clear ctx.
      ginduction mds_tgt; i; ss.
      econs; cycle 1. { rewrite Sk.add_assoc. apply IHmds_tgt. }
      ss. etrans; [|apply Sk.le_canon]. etrans; [|apply Sk.le_add_l].
      apply Sk.le_add_r. }
    { inv SKWF. rewrite <- SKEQ. apply Sk.wf_canon; et. }
    intro SIM.
    destruct wf_tgt; cycle 1.
    { exfalso. apply n. unfold ModL.wf in *. ss.
      fold sk_tgt. rewrite <- SKEQ. des. split; et. ss.
      inv WF. econs; ss; rewrite map_app in *.
      - i. set (List.map fst _) as ndom_src at 2.
        set (List.map fst _) as ndom_tgt in wf_fnsems at 2.
        replace ndom_src with ndom_tgt; et.
        unfold ndom_src, ndom_tgt. fold sk_src. rewrite SKEQ. clear -SIM. clearbody sk_tgt.
        revert mds_tgt SIM. induction mds_src; i. 
        { inv SIM. destruct mds_tgt; clarify. }
        destruct mds_tgt; inv SIM. ss. do 2 rewrite map_app. f_equal; et.
        inv H3. clear -sim_fnsems.
        set (ModSem.fnsems _) as fl1. set (ModSem.fnsems _) as fl2. 
        fold fl1 in sim_fnsems. fold fl2 in sim_fnsems.
        clearbody fl1 fl2. revert fl2 sim_fnsems.
        induction fl1; i; destruct fl2; inv sim_fnsems; ss.
        f_equal; et. inv H3. destruct a0, p. ss.
      - i. set (List.map fst _) as ndom_src at 2.
        set (List.map fst _) as ndom_tgt in wf_initial_mrs at 2.
        replace ndom_src with ndom_tgt; et.
        unfold ndom_src, ndom_tgt. fold sk_src. rewrite SKEQ. clear -SIM. clearbody sk_tgt.
        revert mds_tgt SIM. induction mds_src; i. 
        { inv SIM. destruct mds_tgt; clarify. }
        destruct mds_tgt; inv SIM. ss. inv H3. f_equal; et. }
    ss. rewrite SKEQ.
    red in SIM. inv w. rename H0 into MSWFTGT. red in MSWFTGT. ss. fold sk_tgt in MSWFTGT. 
    clearbody sk_tgt. clear -SIM PR MSWFTGT.
    revert mds_tgt SIM ctx MSWFTGT x0 PR.
    induction mds_src; i.
    { destruct mds_tgt; inv SIM. ss. }
    destruct mds_tgt; inv SIM. rewrite Mod.add_list_cons in *. ss.
    rewrite ModSemL.add_assoc_eq in *. 
    change (ModSemL.add (ModL.get_modsem (Mod.add_list ctx) (Sk.canon sk_tgt)) (Mod.get_modsem a (Sk.canon sk_tgt)))
      with (ModL.get_modsem (ModL.add (Mod.add_list ctx) a) (Sk.canon sk_tgt)).
    change (ModSemL.add (ModL.get_modsem (Mod.add_list ctx) (Sk.canon sk_tgt)) (Mod.get_modsem t (Sk.canon sk_tgt)))
      with (ModL.get_modsem (ModL.add (Mod.add_list ctx) t) (Sk.canon sk_tgt)) in MSWFTGT.
    assert (MSWFSRC: ModSemL.wf (ModSemL.add (ModL.get_modsem (ModL.add (Mod.add_list ctx) a) (Sk.canon sk_tgt)) (ModL.get_modsem (Mod.add_list mds_tgt) (Sk.canon sk_tgt)))).
    { clear -MSWFTGT H3. inv MSWFTGT. econs; ss; rewrite ! map_app in *; cycle 1.
      { inv H3. rewrite sim_mn. ss. }
      set (List.map fst (List.map _ _)) as anamedom.
      set (List.map fst (List.map _ _)) as tnamedom in wf_fnsems.
      replace anamedom with tnamedom; et.
      unfold tnamedom, anamedom. inv H3. clear -sim_fnsems.
      induction sim_fnsems; auto.
      ss. f_equal; ss. inv H0. destruct x, y. ss. }
    rewrite <- ! Mod.add_list_snoc in *.
    eapply IHmds_src; [>et..|]. inv H3. des. 
    rewrite ! Mod.add_list_snoc in *.
    eapply adequacy_local_aux with (wf:=wf) (mn:= ModSem.mn (Mod.get_modsem a (Sk.canon sk_tgt))); et.
    - i. ss. rewrite ! alist_find_app_o.
      destruct (alist_find fn (ModSemL.fnsems (ModL.get_modsem (Mod.add_list ctx) (Sk.canon sk_tgt)))) eqn: E.
      { right. left. set ctx as ctx0 in E.
        assert (INV: List.incl ctx0 ctx) by refl.
        clearbody ctx0. revert ctx0 E INV. induction ctx0; i; ss.
        rewrite alist_find_app_o in E. des_ifs; cycle 1.
        { eapply IHctx0; et. etrans; et. unfold incl. ss. et. }
        clear -INV Heq MSWFSRC. unfold map_snd in Heq.
        rewrite alist_find_map in Heq. uo. des_ifs. 
        exists (ModSem.mn (Mod.get_modsem a0 (Sk.canon sk_tgt))), i0.
        esplits; ss.
        inv MSWFSRC. ss. rewrite ! map_app in *. ss. apply nodup_app_l in wf_initial_mrs.
        apply nodup_comm in wf_initial_mrs. ss. apply NoDup_cons_iff in wf_initial_mrs.
        des. red. i. apply wf_initial_mrs. rewrite H0. clear -INV. unfold incl in *.
        hexploit INV. { ss. auto. } i.  clear -H0. ginduction ctx; i; ss; des; subst; et. }
      destruct (alist_find fn (List.map _ _)) eqn: E1.
      { right. right. des_ifs; cycle 1.
        { exfalso. clear -sim_fnsems E1 Heq. induction sim_fnsems; ss.
          inv H0. destruct x, y. red in H1, H2. ss. subst. des_ifs. et. }
        induction sim_fnsems; ss.
        inv H0. destruct x, y. red in H1, H2. ss. subst. des_ifs; et.
        eexists _, _. esplits; et. rewrite sim_mn. ss. }
      destruct (alist_find fn (ModSemL.fnsems (ModL.get_modsem (Mod.add_list mds_tgt) _))) eqn: E2; et.
      right. left. des_ifs.
      { exfalso. clear -sim_fnsems E1 Heq. induction sim_fnsems; ss.
        inv H0. destruct x, y. red in H1, H2. ss. subst. des_ifs. et. }
      inv MSWFSRC. ss. rewrite ! map_app in wf_initial_mrs. rewrite <- List.app_assoc in wf_initial_mrs.
      apply nodup_app_r in wf_initial_mrs. ss. apply NoDup_cons_iff in wf_initial_mrs.
      des. clear -wf_initial_mrs E2.
      induction mds_tgt; ss.
      rewrite alist_find_app_o in E2. des_ifs; et. unfold map_snd in Heq.
      rewrite alist_find_map in Heq. uo. des_ifs.
      eexists _,_. esplits; et.
    - exists w_init. econs;[refl|..]; cycle 1.
      { i. unfold ModSemL.initial_p_state. ss. 
        rewrite ! alist_find_app_o. ss. rewrite ! eq_rel_dec_correct. des_ifs. }
      rewrite sim_mn at 2. unfold ModSemL.initial_p_state. ss.
      rewrite ! alist_find_app_o. ss. rewrite ! eq_rel_dec_correct.
      do 2 (destruct (string_Dec _ _); clarify).
      destruct (alist_find _ _) eqn: E at 1.
      { exfalso. apply alist_find_some in E. clear -MSWFSRC E. inv MSWFSRC.
        ss. rewrite ! map_app in *. ss. apply nodup_app_l in wf_initial_mrs.
        apply nodup_comm in wf_initial_mrs. ss. apply NoDup_cons_iff in wf_initial_mrs.
        des. apply wf_initial_mrs. eapply in_map with (f:=fst) in E. ss. }
      destruct (alist_find _ _) eqn: E1 at 1; et.
      exfalso. apply alist_find_some in E1. clear -MSWFTGT E1. inv MSWFTGT.
      ss. rewrite ! map_app in *. ss. apply nodup_app_l in wf_initial_mrs.
      apply nodup_comm in wf_initial_mrs. ss. apply NoDup_cons_iff in wf_initial_mrs.
      des. apply wf_initial_mrs. eapply in_map with (f:=fst) in E1. ss.
  Qed.

  Theorem adequacy_local_strong md_src md_tgt
          (SIM: ModPair.sim md_src md_tgt)
    :
      <<CR: (refines_strong md_tgt md_src)>>
  .
  Proof.
    replace (Mod.lift md_tgt) with (Mod.add_list [md_tgt]).
    2:{ unfold Mod.add_list. ss. rewrite ModL.add_empty_r. ss. }
    replace (Mod.lift md_src) with (Mod.add_list [md_src]).
    2:{ unfold Mod.add_list. ss. rewrite ModL.add_empty_r. ss. }
    apply adequacy_local_strong_l. i. inv SIM. econs; ss; cycle 1.
    { econs; et. }
    i. econs; et. eapply sim_modsem; et. inv SKINCL. ss.
  Qed.

  Context {CONF: EMSConfig}.

  Theorem adequacy_local md_src md_tgt
          (SIM: ModPair.sim md_src md_tgt)
    :
      <<CR: (refines md_tgt md_src)>>
  .
  Proof.
    eapply ModSem.refines_strong_refines.
    eapply adequacy_local_strong; et.
  Qed.

  Corollary adequacy_local_list_strong
            mds_src mds_tgt
            (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt)
    :
      <<CR: refines_strong (Mod.add_list mds_tgt) (Mod.add_list mds_src)>>
  .
  Proof.
    r. induction FORALL; ss.
    { ii. auto. }
    rewrite ! Mod.add_list_cons.
    etrans.
    { rewrite <- Mod.add_list_single. eapply refines_strong_proper_r.
      rewrite ! Mod.add_list_single. eapply adequacy_local_strong; et. }
    replace (Mod.lift x) with (Mod.add_list [x]); cycle 1.
    { cbn. rewrite ModL.add_empty_r. refl. }
    eapply refines_strong_proper_l; et.
  Qed.

  Theorem adequacy_local2 md_src md_tgt
          (SIM: ModPair.sim md_src md_tgt)
    :
      <<CR: (refines2 [md_tgt] [md_src])>>
  .
  Proof.
    eapply ModSem.refines_strong_refines.
    eapply adequacy_local_list_strong. econs; ss.
  Qed.

  Corollary adequacy_local_list
            mds_src mds_tgt
            (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt)
    :
      <<CR: refines (Mod.add_list mds_tgt) (Mod.add_list mds_src)>>
  .
  Proof.
    eapply ModSem.refines_strong_refines.
    eapply adequacy_local_list_strong; et.
  Qed.

End ADEQUACY.