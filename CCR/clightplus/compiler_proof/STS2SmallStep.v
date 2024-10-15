From compcert Require Import Smallstep Clight Integers Values Events Behaviors.
Require Import CoqlibCCR.
Require Import Any.
Require Import STS.
Require Import Behavior.

Set Implicit Arguments.




Section Beh.

  Variable gvmap : AST.ident -> option Z.

  Inductive match_val : eventval -> Any.t -> Prop :=
  | match_val_long : forall l, match_val (EVlong l) (Int64.signed l)↑
  | match_val_int : forall i, match_val (EVint i) (Int.signed i)↑
  | match_val_ptr id ofs : match_val (EVptr_global id ofs) (id, Ptrofs.unsigned ofs)↑
  | match_val_ptr_long id ofs l (ARCH: Archi.ptr64 = true) (CAST: to_int_ev id ofs gvmap = Some (Vlong l)) : match_val (EVlong l) (id, Ptrofs.unsigned ofs)↑
  | match_val_ptr_int id ofs i (ARCH: Archi.ptr64 = false) (CAST: to_int_ev id ofs gvmap = Some (Vint i)) : match_val (EVint i) (id, Ptrofs.unsigned ofs)↑.

  Inductive match_event : Events.event -> STS.event -> Prop :=
  | match_event_intro
      name eargs uargs er ur
      (MV: Forall2 match_val eargs uargs)
      (MV: match_val er ur)
    :
      match_event (Event_syscall name eargs er) (event_sys name uargs ur)
  .

  Variant _match_beh (match_beh: _ -> _ -> Prop) (tgtb : program_behavior) (srcb : Tr.t) : Prop :=
  | match_beh_Terminates
      tr mtr r
      (MT : Forall2 match_event tr mtr)
      (TB : tgtb = Terminates tr r)
      (SB : srcb = Tr.app mtr (Tr.done r↑))
    :
      _match_beh match_beh tgtb srcb
  | match_beh_Diverges
      tr mtr
      (MT : Forall2 match_event tr mtr)
      (TB : tgtb = Diverges tr)
      (SB : srcb = Tr.app mtr (Tr.spin))
    :
      _match_beh match_beh tgtb srcb
  | match_beh_Reacts
      ev mev trinf mtrinf
      (ME : match_event ev mev)
      (MB : match_beh (Reacts trinf) mtrinf)
      (TB : tgtb = Reacts (Econsinf ev trinf))
      (SB : srcb = Tr.cons mev mtrinf)
    :
      _match_beh match_beh tgtb srcb
  | match_beh_ub_trace
      mtr tr
      (SB : srcb = Tr.app mtr (Tr.ub))
      (MT : Forall2 match_event tr mtr)
      (TB : behavior_prefix tr tgtb)
    :
      _match_beh match_beh tgtb srcb
  | match_beh_PTerm
      mtr tr
      (TB : tgtb = Partial_terminates tr)
      (MT : Forall2 match_event tr mtr)
      (SB : Tr.prefix mtr srcb)
    :
      _match_beh match_beh tgtb srcb.

  Definition match_beh : _ -> _ -> Prop := paco2 _match_beh bot2.

  Lemma match_beh_mon : monotone2 _match_beh.
  Proof.
    ii. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
    - econs 5; eauto.
  Qed.


End Beh.
Hint Constructors _match_beh.
Hint Unfold match_beh.
Hint Resolve match_beh_mon: paco.

Lemma match_val_map_mon gm0 gm1 ev a
  (LE: Simulation.gm_improves gm0 gm1)
  (M0: match_val gm0 ev a)
:
  match_val gm1 ev a.
Proof.
  inv M0; econs; et.
  - unfold to_int_ev in *. des_ifs.
    all: unfold Simulation.gm_improves in LE; hexploit LE; et; i; clarify.
  - unfold to_int_ev in *. des_ifs.
    all: unfold Simulation.gm_improves in LE; hexploit LE; et; i; clarify.
Qed.

Lemma match_event_map_mon gm0 gm1 ev a
  (LE: Simulation.gm_improves gm0 gm1)
  (M0: match_event gm0 ev a)
:
  match_event gm1 ev a.
Proof.
  inv M0; econs; et; cycle 1.
  { eapply match_val_map_mon; et. }
  clear -MV LE. induction MV; et. econs; et.
  eapply match_val_map_mon; et.
Qed.

Lemma match_beh_map_mon gm0 gm1 tr_src tr_tgt
  (LE: Simulation.gm_improves gm0 gm1)
  (M0: match_beh gm0 tr_src tr_tgt)
:
  match_beh gm1 tr_src tr_tgt.
Proof.
  revert tr_src tr_tgt M0. pcofix CIH. i.
  punfold M0. inv M0.
  - pfold. econs. 2,3: et.
    clear -MT LE. induction MT; et. econs; et.
    eapply match_event_map_mon; et.
  - pfold. econs 2. 2,3: et.
    clear -MT LE. induction MT; et. econs; et.
    eapply match_event_map_mon; et.
  - pfold. econs 3. 3,4: et.
    { eapply match_event_map_mon; et. }
    pclearbot. right. apply CIH. apply MB.
  - pfold. econs 4. 1,3: et.
    clear -MT LE. induction MT; et. econs; et.
    eapply match_event_map_mon; et.
  - pfold. econs 5. 1,3: et.
    clear -MT LE. induction MT; et. econs; et.
    eapply match_event_map_mon; et.
Qed.





(* behavior improve statement for state *)
Definition improves2 {L0 L1} (gvmap : AST.ident -> option Z) (st_src0: L0.(STS.state)) (st_tgt0: L1.(Smallstep.state)): Prop :=
  forall tr_tgt (BEH: state_behaves L1 st_tgt0 tr_tgt),
  exists tr_src, (<<BEH: (Beh.of_state L0 st_src0) tr_src>>) /\
                 (<<SIM: match_beh gvmap tr_tgt tr_src>>)
.

(* behavior improve statement for program *)
(* Program in STS has no meta-map currently, interpreted as empty map so that STS is always greater than Smallstep *)
Definition improves2_program (L0: STS.semantics) (L1: Smallstep.semantics) : Prop :=
  forall gvmap tr_tgt (BEH: program_observes L1 (gvmap, tr_tgt)),
  match gvmap with
  | Some gvmap => exists tr_src, (<<BEH: (Beh.of_state L0 L0.(initial_state)) tr_src>>)
                  /\ (<<SIM: match_beh gvmap tr_tgt tr_src>>)
  | None => True
  end
.

Definition improves (L0 L1: STS.semantics): Prop :=
  Beh.improves (Beh.of_program L0) (Beh.of_program L1)
.

Lemma improves_combine: forall (S I: STS.semantics) (A: Smallstep.semantics),
    improves S I -> improves2_program I A -> improves2_program S A.
Proof.
  i. ii. exploit H0; et. i. destruct gvmap; et.
  des. exists tr_src. esplits; et. eapply H; et.
Qed.

Lemma improves2_map_mon L0 L1 gm0 gm1 st_src st_tgt
  (LE: Simulation.gm_improves gm0 gm1)
  (M0: @improves2 L0 L1 gm0 st_src st_tgt)
:
  improves2 gm1 st_src st_tgt.
Proof.  unfold improves2 in *. i. hexploit M0; et. i. des. hexploit match_beh_map_mon; et. Qed.

Lemma match_event_trans o o1 x y y0
  (R1: match_event o1 x y)
  (R2: ev_rel o x y0)
  (LE: Simulation.gm_improves o1 o)
:
  match_event o y0 y.
Proof.
  unfold ev_rel, event_rel in R2.
  des_ifs; des; unfold lib.sflib.NW in *; clarify; inv R1.
  econs.
  - clear - MV R0 LE. revert uargs MV. induction R0; i; ss; inv MV; econs; et.
    unfold evval_rel, eventval_bind in H.
    des_ifs; des; unfold lib.sflib.NW in *; clarify.
    all: inv H2; econs; et.
    + unfold to_int_ev in *. des_ifs.
    + unfold to_int_ev in CAST.
      des_ifs. apply LE in Heq. unfold to_int_ev. des_ifs.
  - unfold evval_rel, eventval_bind in R3.
    des_ifs; des; unfold lib.sflib.NW in *; clarify.
    all: inv MV0; econs; et.
    + unfold to_int_ev in *. des_ifs.
    + unfold to_int_ev in CAST.
      des_ifs. apply LE in Heq. unfold to_int_ev. des_ifs.
Qed.

Lemma match_events_trans o o1 t t' mtr
  (R1: Forall2 (match_event o1) t mtr)
  (R2: tr_rel (ev_rel o) t t')
  (LE: Simulation.gm_improves o1 o)
:
  Forall2 (match_event o) t' mtr.
Proof.
  unfold tr_rel in R2.
  revert_until R1. revert t'.
  ginduction R1; i; ss; inv R2; econs; et.
  eapply match_event_trans; et.
Qed.

Lemma tr_app_trans tl1 tl2 tr
:
  Tr.app tl1 (Tr.app tl2 tr) = Tr.app (tl1 ++ tl2) tr.
Proof. ginduction tl1; ss. i. f_equal; et. Qed.

Lemma tr_app_inf o t t0 mtrinf
  (M: match_beh o (Reacts (t *** t0)) mtrinf)
:
  (exists l t', mtrinf = Tr.app l Tr.ub
    /\ behavior_prefix t' (Reacts (t *** t0)) /\ Forall2 (match_event o) t' l)
  \/
  exists l0 t0', mtrinf = Tr.app l0 t0'
    /\ Forall2 (match_event o) t l0
    /\ match_beh o (Reacts t0) t0'.
Proof.
  ginduction t; i; ss.
  - punfold M. inv M; clarify.
    + right. pclearbot. exists []. esplits; et; ss.
      pfold. econs 3; et.
    + left. esplits; et.
  - punfold M. inv M; clarify.
    + pclearbot. hexploit IHt; et. i. des; clarify.
      * left. rewrite Tr.fold_app. esplits; et.
        2:{ econs; et. } unfold behavior_prefix in *. des; clarify.
        exists beh'. destruct beh'; ss; clarify. rewrite H0. et.
      * right. rewrite Tr.fold_app. esplits; et.
    + left. esplits; et.
Qed.

Lemma tr_app_compare t t0 t1 t2
  (EQ: t *** t0 = t1 *** t2)
:
  (exists l, t ++ l = t1) \/ (exists l, t1 ++ l = t).
Proof.
  ginduction t; i; ss.
  - left. esplits; et.
  - destruct t1; ss; clarify.
    + right. esplits; et.
    + apply IHt in H0. des; clarify; et.
Qed.

Lemma beh_app_compare t t1 beh beh0
  (EQ: behavior_app t beh = behavior_app t1 beh0)
:
  (exists l, t ++ l = t1) \/ (exists l, t1 ++ l = t).
Proof.
  ginduction t; i; ss.
  - left. esplits; et.
  - destruct t1; ss; clarify.
    + right. esplits; et.
    + hexploit (IHt t1 beh beh0).
      * clear - EQ. unfold behavior_app in *. des_ifs; f_equal; et.
      * i. assert (a = e); cycle 1. des; clarify; et.
        clear - EQ. unfold behavior_app in EQ. des_ifs.
Qed.

Theorem improves2_program_observe_trans L1 L2 L3
  (LAYER1: improves2_program L1 L2)
  (LAYER2: forall obs1, program_observes L3 obs1 -> exists obs0, program_observes L2 obs0 /\ observation_improves obs0 obs1)
:
  improves2_program L1 L3.
Proof.
  unfold improves2_program in *. i. des_ifs.
  hexploit LAYER2; et. i. des. destruct obs0; ss.
  inv H0. ss. unfold gm_improves' in H2. des_ifs.
  apply LAYER1 in H. des. esplits; et.
  clear -SIM H1 H2. revert p tr_tgt tr_src H1 SIM.
  pcofix CIH. i. punfold SIM. inv SIM.
  - inv H1.
    + ss. des_ifs. des. clarify. pfold. econs 1. 2,3: et.
      eapply match_events_trans; et.
    + des; clarify. destruct H1. destruct x; ss. clarify.
      hexploit Forall2_app_inv_l; et. i. des. clarify.
      pfold. econs 5. et.
      { eapply match_events_trans. 2: et. et. et. }
      { unfold Tr.prefix. eexists. apply tr_app_trans. }
  - inv H1.
    + ss. des_ifs. pfold. econs 2. 2,3: et.
      eapply match_events_trans; et.
    + des; clarify. destruct H1. destruct x; ss. clarify.
      hexploit Forall2_app_inv_l; et. i. des. clarify.
      pfold. econs 5. et.
      { eapply match_events_trans. 2: et. et. et. }
      { unfold Tr.prefix. eexists. apply tr_app_trans. }
  - pclearbot. inv H1.
    + ss. des_ifs. pfold. punfold H. inv H. pclearbot.
      econs 3. 3,4: et. eapply match_event_trans; et.
      right. eapply CIH. 2:et. unfold behavior_improves. ss. et.
    + des; clarify. destruct H1. destruct x; ss. clarify.
      destruct t. { inv H0. pfold. econs 5; et. rr. eexists. ss. }
      ss. clarify. inv H0. hexploit tr_app_inf; et. i. des; clarify.
      * pfold. rewrite Tr.fold_app. unfold behavior_prefix in H0.
        des. destruct beh'; ss; clarify.
        hexploit tr_app_compare; et. i. des; clarify.
        { hexploit Forall2_app_inv_l; et. i. des. clarify.
          econs 5; et.
          { econs. eapply match_event_trans; et. eapply match_events_trans. apply H. et. et. }
          rr. rewrite Tr.fold_app. rewrite app_comm_cons. rewrite <- tr_app_trans. et. }
        { hexploit Forall2_app_inv_l; et. i. des. clarify.
          econs 4. { rewrite Tr.fold_app. et. }
          { econs. eapply match_event_trans; et. eapply match_events_trans; et. }
          rr. rewrite app_comm_cons. exists (Partial_terminates l2'). et. }
      * pfold. econs 5; et. { econs. eapply match_event_trans; et. eapply match_events_trans; et. }
        rr. eexists. ss.
  - unfold behavior_improves in H1. des; clarify.
    + hexploit prefix_tr_rel; et. i. des. pfold. econs 4; et.
      eapply match_events_trans; et.
    + unfold behavior_prefix in TB. des. destruct beh'; ss; clarify.
      unfold tr_rel in H0.
      hexploit Forall2_app_inv_l; et. i. des. clarify.
      pfold. econs 4. et. eapply match_events_trans; et.
      unfold behavior_prefix in *. des. clarify.
      rewrite behavior_app_assoc. et.
    + unfold behavior_prefix in *. des. clarify. pfold.
      hexploit beh_app_compare; et. i. des; clarify.
      { hexploit Forall2_app_inv_l; et. i. des. clarify.
        econs 5; et.
        { eapply match_events_trans. apply H. et. et. }
        rr. rewrite <- tr_app_trans. et. }
      { hexploit Forall2_app_inv_l; et. i. des. clarify.
        econs 4; et.
        { eapply match_events_trans; et. }
        rr. exists (Partial_terminates l2'). et. }
  - unfold behavior_improves in H1. des; clarify.
    + ss. des_ifs. hexploit match_events_trans; et.
    + unfold behavior_prefix in *. des.
      unfold Tr.prefix in *. des. clarify.
      destruct beh'; ss; clarify.
      hexploit Forall2_app_inv_l; et. i. des. clarify.
      rewrite <- tr_app_trans. pfold. econs 5; et.
      eapply match_events_trans. apply H. all: et.
      rr. et.
Qed.



(************************ Coq Aux ****************************)
(************************ Coq Aux ****************************)
(************************ Coq Aux ****************************)
Fixpoint sequence X (xs: list (option X)): option (list X) :=
  match xs with
  | nil => Some nil
  | Some hd :: tl => do tl <- (sequence tl); Some (hd :: tl)
  | None :: _ => None
  end
.

(*** it is basically sequence with return type (Err (list X) (list X)). ***)
(*** i.e., fails with information ***)
Fixpoint squeeze X (es: list (option X)): ((list X) * bool) :=
  match es with
  | [] => ([], true)
  | Some e :: tl => let '(es, succ) := squeeze tl in ((e :: es), succ)
  | _ => ([], false)
  end
.

Lemma squeeze_app X (l0 l1: list (option X))
  :
    squeeze (l0 ++ l1) =
    let '(l0', b0) := squeeze l0 in
    if b0
    then let '(l1', b1) := squeeze l1 in (l0'++l1', b1)
    else (l0', false).
Proof.
  revert l1. induction l0; ss.
  { i. des_ifs. }
  { i. des_ifs.
    { rewrite IHl0 in Heq. rewrite Heq1 in *. clarify. }
    { rewrite IHl0 in Heq. clarify. }
  }
Qed.

Definition option_to_list X (x: option X): list X :=
  match x with
  | Some x => [x]
  | _ => []
  end
.
Coercion option_to_list: option >-> list.
Hint Constructors Forall2.

(************************ Tgt Aux ****************************)
(************************ Tgt Aux ****************************)
(************************ Tgt Aux ****************************)
Definition single_events_at (L: Smallstep.semantics) (s:L.(Smallstep.state)) : Prop :=
  forall t s', Step L s t s' -> (t = E0).

Record wf_at (L: Smallstep.semantics) (s:L.(Smallstep.state)) : Prop :=
  Wf_at {
      wf_at_final:
        forall tr s' retv
               (FINAL: Smallstep.final_state L s retv)
               (STEP: Step L s tr s'),
          False;
      wf_at_final_determ:
        forall retv0 retv1
               (FINAL0: Smallstep.final_state L s retv0)
               (FINAL1: Smallstep.final_state L s retv1),
          (<<EQ: retv0 = retv1>>);
    }.

Definition wf_semantics (L: Smallstep.semantics) : Prop :=
  forall st, wf_at L st.

(* Record strict_determinate_at (L: Smallstep.semantics) (s:L.(Smallstep.state)) : Prop := *)
(*   Strict_determinate_at { *)
(*       ssd_determ_at: forall t1 s1 t2 s2 *)
(*         (STEP0: Step L s t1 s1) *)
(*         (STEP1 :Step L s t2 s2), *)
(*         <<EQ: s1 = s2>>; *)
(*     ssd_determ_at_final: forall tr s' retv *)
(*         (FINAL: Smallstep.final_state L s retv) *)
(*         (STEP: Step L s tr s'), *)
(*         False; *)
(*     ssd_traces_at: *)
(*       single_events_at L s *)
(*   }. *)

(************************ Src Aux ****************************)
(************************ Src Aux ****************************)
(************************ Src Aux ****************************)



Definition wf (L: semantics) (st0: L.(state)): Prop :=
  forall (ANG: L.(state_sort) st0 = angelic),
  forall st1 st1' (STEP: step L st0 None st1) (STEP: step L st0 None st1'), st1 = st1'
.



Section STAR.
(* there's well formed path s.t. st_src0 ->_es st_src1 *)
  Variable L: semantics.
  Variable P: L.(state) -> Prop.
  Inductive pstar: L.(state) -> list event -> L.(state) -> Prop :=
  | star_refl: forall st_src0, pstar st_src0 [] st_src0
  | star_step: forall
      st_src0 es0 st_src1 es1 st_src2
      (P: P st_src0)
      (HD: step L st_src0 es0 st_src1)
      (TL: pstar st_src1 es1 st_src2)
    ,
      pstar st_src0 (es0 ++ es1) st_src2
  .
End STAR.
Hint Constructors pstar.
Definition dstar L := pstar L (fun st_src0 => L.(state_sort) st_src0 = demonic).
Definition star L := pstar L (wf L).

Lemma star_trans
      L
      st0 st1 st2 es0 es1
      (STEPS0: star L st0 es0 st1)
      (STEPS1: star L st1 es1 st2)
  :
    star L st0 (es0 ++ es1) st2.
Proof.
  revert es1 st2 STEPS1. induction STEPS0; et.
  i. rewrite <- List.app_assoc.
  econs; et. eapply IHSTEPS0. et.
Qed.

Lemma star_des
      L
      st0 e es st2
      (STAR: star L st0 (e :: es) st2)
  :
    exists st1, <<HD: star L st0 [e] st1>> /\ <<TL: star L st1 es st2>>
.
Proof.
  remember (e :: es) as x. revert Heqx. revert e es.
  induction STAR; ii; ss.
  destruct es0; ss.
  - clarify. esplits; et. change [e] with ((option_to_list (Some e)) ++ []).
    econs; ss; et.
  - subst. exploit IHSTAR; et. i; des. esplits; et.
    change [e] with ((@option_to_list event None) ++ [e]).
    econs; ss; et.
Qed.


Lemma star_event_ind
      L
      (P: L.(state) -> list event -> L.(state) -> Prop)
      (BASE: forall st0 st1, star L st0 [] st1 -> P st0 [] st1)
      (SUCC: forall e es st0 st1 st2, star L st0 [e] st1 -> star L st1 es st2 ->
                                      P st1 es st2 -> P st0 (e :: es) st2)
  :
    forall st0 es st1, star L st0 es st1 -> P st0 es st1
.
Proof.
  fix IH 2.
  i.
  destruct es; ss.
  - eapply BASE. ss.
  - eapply star_des in H. des. rename st2 into st_mid.
    eapply SUCC.
    { et. }
    { et. }
    eapply IH.
    eapply TL.
Qed.

Lemma star_single_exact
      L0 st0 st3 e0
      (STAR: star L0 st0 [e0] st3)
  :
    exists st1 st2, (<<STAR: star L0 st0 [] st1>>) /\
                    (<<VIS: step L0 st1 (Some e0) st2>>) /\
                    (<<STAR: star L0 st2 [] st3>>)
.
Proof.
  dependent induction STAR; ii; ss.
  destruct es0; ss.
  { destruct es1; ss. clarify. esplits; et. econs. }
  clarify.
  exploit IHSTAR; et. i; des. esplits; try apply VIS; et.
  replace [] with ((@option_to_list event None) ++ []) by ss.
  econs; et.
Qed.

Definition NoStuck L (st_src0: state L): Prop :=
  L.(state_sort) st_src0 = angelic ->
  (<<NOSTUCK: exists ev st_src1, step L st_src0 ev st_src1>>)
(* (<<DTM: forall st_src1 st_src1', *)
(*     step L st_src0 None st_src1 -> *)
(*     step L st_src0 None st_src1' -> *)
(*     st_src1 = st_src1'>>) *)
.



(* Definition wf (L: semantics): Prop := *)
(*   forall (st0: L.(state)) (ANG: L.(state_sort) st0 = angelic), *)
(*   forall st1 st1' (STEP: step L st0 None st1) (STEP: step L st0 None st1'), st1 = st1' *)
(* . *)


Section BEH.

Variable L: semantics.
(* Hypothesis WFSRC: wf L. *)
(* Hypothesis WFSRC: forall st, (state_sort L st = angelic) -> wf L st. *)

(*** TODO: move to proper place? ***)
Lemma _beh_astep_rev
      r tr st0 ev st1
      (SRT: _.(state_sort) st0 = angelic)
      (WFSRC: wf _ st0)
      (STEP: _.(step) st0 ev st1)
      (BEH: paco2 (Beh._of_state L) r st1 tr)
  :
    <<BEH: paco2 (Beh._of_state L) r st0 tr>>
.
Proof.
  exploit wf_angelic; et. i; clarify.
  pfold. econsr; ss; et. rr. ii. exploit wf_angelic; et. i; des. subst.
  exploit WFSRC; [..|apply STEP|apply STEP0|]; ss. i; subst. esplits; et.
  punfold BEH.
Qed.

Lemma beh_of_state_star
      r st_src0 st_src1 es0 tr1
      (BEH: paco2 (Beh._of_state L) r st_src1 tr1)
      (STAR: star L st_src0 es0 st_src1)
  :
    <<BEH: paco2 (Beh._of_state L) r st_src0 (Tr.app es0 tr1)>>
.
Proof.
  revert BEH. revert tr1.
  induction STAR; ii; ss.
  exploit IHSTAR; et.
  intro U; des.
  destruct (state_sort L st_src0) eqn:T.
  - exploit wf_angelic; et. i; subst. ss.
    eapply _beh_astep_rev; et.
  - exploit wf_demonic; et. i; subst. ss.
    pfold. econs; ss; et. rr. esplits; ss; et. punfold U.
  - exploit wf_final; et. ss.
  - destruct es0; ss; cycle 1.
    { exploit wf_vis_event; et. ss. }
    pfold; econs; ss; et.
Qed.

Variant starC (r: (state L -> Tr.t -> Prop)): (state L -> Tr.t -> Prop) :=
| starC_intro
    st0 st1 tr
    (STAR: star L st0 [] st1)
    (SIM: r st1 tr)
  :
    starC r st0 tr
.

Hint Constructors starC: core.

Lemma starC_mon
      r1 r2
      (LE: r1 <2= r2)
  :
    starC r1 <2= starC r2
.
Proof. ii. destruct PR; econs; et. Qed.

Hint Resolve starC_mon: paco.

Lemma starC_prespectful: prespectful2 (Beh._of_state L) starC.
Proof.
  econs; eauto with paco.
  ii. rename x0 into st0. rename x1 into tr.
  inv PR. rename st2 into st1.
  apply GF in SIM.
  { change tr with (Tr.app [] tr). eapply beh_of_state_star; et. pfold.
    eapply Beh.of_state_mon; et.
  }
Qed.

Lemma starC_spec: starC <3= gupaco2 (Beh._of_state L) (cpn2 (Beh._of_state L)).
Proof. intros. eapply prespect2_uclo; eauto with paco. eapply starC_prespectful. Qed.

Variant starC2 (r: (state L -> Tr.t -> Prop)): (state L -> Tr.t -> Prop) :=
| starC2_intro
    st0 st1 tr0 tr1
    (STAR: star L st0 tr0 st1)
    (SIM: r st1 tr1)
  :
    starC2 r st0 (Tr.app tr0 tr1)
.

Hint Constructors starC2: core.

Lemma starC2_mon
      r1 r2
      (LE: r1 <2= r2)
  :
    starC2 r1 <2= starC2 r2
.
Proof. ii. destruct PR; econs; et. Qed.

Hint Resolve starC2_mon: paco.

Lemma starC2_prespectful: prespectful2 (Beh._of_state L) starC2.
Proof.
  econs; eauto with paco.
  ii. rename x0 into st0. rename x1 into tr.
  inv PR. rename st2 into st1.
  apply GF in SIM.
  { eapply beh_of_state_star; ss; et. pfold.
    eapply Beh.of_state_mon; et.
  }
Qed.

Lemma starC2_spec: starC2 <3= gupaco2 (Beh._of_state L) (cpn2 (Beh._of_state L)).
Proof. intros. eapply prespect2_uclo; eauto with paco. eapply starC2_prespectful. Qed.


End BEH.

(************************ Decompile ****************************)
(************************ Decompile ****************************)
(************************ Decompile ****************************)

Definition decompile_eval (ev: eventval): option Any.t :=
  match ev with
  | EVlong l => Some (Int64.signed l)↑
  | EVint i => Some (Int.signed i)↑
  | EVptr_global id ofs => Some (id, Ptrofs.unsigned ofs)↑
  | _ => None
  end
.

Definition decompile_event (ev: Events.event): option event :=
  match ev with
  | Event_syscall fn evs ev =>
    do vs <- sequence (List.map decompile_eval evs);
    do v <- decompile_eval ev;
    Some (event_sys fn vs v)
  | _ => None
  end.

(* Definition _decompile_trinf decompile_trinf (tr: traceinf): Tr.t := *)
(*   match tr with *)
(*   | Econsinf ev tr => *)
(*     match decompile_event ev with *)
(*     | Some ev => Tr.cons ev (decompile_trinf tr) *)
(*     | _ => Tr.ub *)
(*     end *)
(*   end *)
(* . *)

(* CoFixpoint decompile_trinf (tr: traceinf): Tr.t := *)
(*   _decompile_trinf decompile_trinf tr. *)
CoFixpoint decompile_trinf (tr: traceinf): Tr.t :=
  match tr with
  | Econsinf ev tr =>
    match decompile_event ev with
    | Some ev => Tr.cons ev (decompile_trinf tr)
    | _ => Tr.ub
    end
  end
.

Variant _Tr: Type :=
| _Tr_done (retv: Any.t)
| _Tr_spin
| _Tr_ub
| _Tr_nb
| _Tr_cons (hd: event) (tl: Tr.t)
.

Definition match_Tr (tr: Tr.t) :=
  match tr with
  | Tr.done retv => _Tr_done retv
  | Tr.spin => _Tr_spin
  | Tr.ub => _Tr_ub
  | Tr.nb => _Tr_nb
  | Tr.cons hd tl => _Tr_cons hd tl
  end.

Lemma Tr_eta (tr0 tr1: Tr.t)
      (EQ: match_Tr tr0 = match_Tr tr1)
  :
    tr0 = tr1.
Proof.
  destruct tr0, tr1; ss; clarify.
Qed.

Lemma unfold_decompile_trinf
      tr
  :
    (decompile_trinf tr) =
    (match tr with
     | Econsinf ev tr =>
       match decompile_event ev with
       | Some ev => Tr.cons ev (decompile_trinf tr)
       | _ => Tr.ub
       end
     end)
.
Proof.
  destruct tr. eapply Tr_eta. ss.
Qed.

Lemma decompile_trinf_app
      tr_tgt tr_src T
      (MB: squeeze (List.map decompile_event tr_tgt) = (tr_src, true))
  :
    (decompile_trinf (tr_tgt *** T)) = Tr.app tr_src (decompile_trinf T)
.
Proof.
  ginduction tr_tgt; ii; ss; clarify.
  des_ifs. ss.
  rewrite unfold_decompile_trinf. des_ifs. f_equal.
  eapply IHtr_tgt; ss.
Qed.

Definition transl_beh (p: program_behavior): Tr.t :=
  match p with
  | Terminates tr i =>
    let '(es, succ) := squeeze (List.map decompile_event tr) in
    Tr.app es (if succ then (Tr.done i↑) else Tr.ub)
  | Diverges tr =>
    let '(es, succ) := squeeze (List.map decompile_event tr) in
    Tr.app es (if succ then (Tr.spin) else Tr.ub)
  | Reacts tr => (decompile_trinf tr)
  | Goes_wrong tr =>
    let '(es, succ) := squeeze (List.map decompile_event tr) in
    Tr.app es Tr.ub
  | Partial_terminates tr =>
    let '(es, succ) := squeeze (List.map decompile_event tr) in
    Tr.app es (if succ then (Tr.nb) else Tr.ub)
  end
.

Lemma decompile_match_val gvmap v0 v1
      (SEQ: decompile_eval v0 = Some v1)
  :
    match_val gvmap v0 v1.
Proof.
  unfold decompile_eval in *. des_ifs; econs.
Qed.

Lemma decompile_match_vals gvmap l0 l1
      (SEQ: sequence (List.map decompile_eval l0) = Some l1)
  :
    Forall2 (match_val gvmap) l0 l1.
Proof.
  revert l1 SEQ. induction l0; ss.
  { i. clarify. }
  { i. uo. des_ifs. econs; et.
    eapply decompile_match_val; et. }
Qed.

Lemma decompile_match_event gvmap
      e0 e1
      (D: decompile_event e0 = Some e1)
  :
    <<M: match_event gvmap e0 e1>>
.
Proof.
  destruct e0; ss. uo. des_ifs. econs.
  { eapply decompile_match_vals; et. }
  { eapply decompile_match_val; et. }
Qed.

Definition null_map : AST.ident -> option Z := fun _ => None.

Lemma match_val_iff v0 v1
  :
    decompile_eval v0 = Some v1 <-> match_val null_map v0 v1.
Proof.
  split.
  { eapply decompile_match_val. }
  i. inv H; ss.
Qed.

Lemma match_vals_iff l0 l1
  :
    sequence (List.map decompile_eval l0) = Some l1 <->
    Forall2 (match_val null_map) l0 l1.
Proof.
  split.
  { eapply decompile_match_vals. }
  revert l1. induction l0; ss.
  { i. inv H. ss. }
  { i. inv H. hexploit IHl0; et. i.
    uo. rewrite H.
    eapply match_val_iff in H2. rewrite H2. ss. }
Qed.

Lemma match_event_iff
      e_src e_tgt
  :
    decompile_event e_tgt = Some e_src <->
    match_event null_map e_tgt e_src
.
Proof.
  split.
  { eapply decompile_match_event. }
  i. inv H. ss. uo.
  eapply match_vals_iff in MV. rewrite MV.
  eapply match_val_iff in MV0. rewrite MV0. ss.
Qed.

Lemma match_event_squeeze
      e_src e_tgt
  :
    squeeze [decompile_event e_tgt] = ([e_src], true) <->
    match_event null_map e_tgt e_src
.
Proof.
  split; i.
  - ss. des_ifs. eapply match_event_iff; et.
  - eapply match_event_iff in H; et. ss. des_ifs.
Qed.

Lemma match_events_squeeze
      es_src es_tgt
  :
    squeeze (List.map decompile_event es_tgt) = (es_src, true) <->
    Forall2 (match_event null_map) es_tgt es_src
.
Proof.
  revert es_tgt. induction es_src; ss.
  { i. split.
    { destruct es_tgt; ss. des_ifs. }
    { i. inv H. ss. }
  }
  { i. split.
    { i. destruct es_tgt; ss. des_ifs.
      hexploit IHes_src; et. i. econs.
      { eapply match_event_squeeze. ss. rewrite Heq. ss. }
      { eapply H. et. }
    }
    { i. inv H. eapply IHes_src in H4. ss.
      eapply match_event_iff in H3. rewrite H3.
      rewrite H4. ss.
    }
  }
Qed.

Theorem decompile_trinf_spec gvmap
        tr
  :
    match_beh gvmap (Reacts tr) (decompile_trinf tr)
.
Proof.
  revert tr.
  pcofix CIH.
  i. destruct tr; ss.
  rewrite unfold_decompile_trinf. des_ifs.
  - eapply decompile_match_event in Heq. dup Heq. inv Heq.
    pfold. eapply match_beh_Reacts; et.
  - pfold. econs 4; ss; et.
    r. esplits; ss; et. rewrite behavior_app_E0. ss.
Qed.








Section SIM.

  Variable L0: STS.semantics.
  Variable L1: Smallstep.semantics.

  Local Open Scope smallstep_scope.

  Inductive _sim sim (f_src f_tgt: bool) (st_src0: L0.(STS.state)) (st_tgt0: L1.(Smallstep.state)): Prop :=
  | sim_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv↑)
      (SRT: _.(Smallstep.final_state) st_tgt0 retv)
    :
      _sim sim f_src f_tgt st_src0 st_tgt0

  | sim_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: forall _st_tgt1, not (Step L1 st_tgt0 E0 _st_tgt1))
      (SRT: exists _ev_tgt _st_tgt1, Step L1 st_tgt0 [_ev_tgt] _st_tgt1)
      (SIM: forall ev_tgt st_tgt1
          (STEP: Step L1 st_tgt0 ev_tgt st_tgt1)
          (NPTERM: ev_tgt <> Some Event_pterm)
        ,
          exists st_src1 ev_src (STEP: _.(step) st_src0 (Some ev_src) st_src1),
            (<<MATCH: Forall2 (match_event null_map) ev_tgt [ev_src]>>) /\
            (<<SIM: sim true true st_src1 st_tgt1>>))
    :
      _sim sim f_src f_tgt st_src0 st_tgt0

  | sim_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: _sim sim true f_tgt st_src1 st_tgt0>>)
    :
      _sim sim f_src f_tgt st_src0 st_tgt0

  | sim_demonic_tgt
      (NOEVENT: forall tr _st_tgt1, Step L1 st_tgt0 tr _st_tgt1 -> tr = E0)
      (SRT: exists _st_tgt1, Step L1 st_tgt0 E0 _st_tgt1)
      (SIM: forall st_tgt1
          (STEP: Step L1 st_tgt0 E0 st_tgt1)
        ,
          <<SIM: _sim sim f_src true st_src0 st_tgt1>>)
    :
      _sim sim f_src f_tgt st_src0 st_tgt0

  (* generated source semantics should have no anglic step <this is for UB> *)
  | sim_angelic_src
      (SRT: _.(state_sort) st_src0 = angelic)
      (DTM: forall st1 st2, (<<DTM1: _.(step) st_src0 None st1>>) -> (<<DTM2: _.(step) st_src0 None st2>>) -> st1 = st2)
      (SIM: forall st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: _sim sim true f_tgt st_src1 st_tgt0>>)
    :
      _sim sim f_src f_tgt st_src0 st_tgt0

  (* case 3 + 4 *)
  | sim_demonic_both
      (SRT: _.(state_sort) st_src0 = demonic)
      (NOEVENT: forall tr _st_tgt1, Step L1 st_tgt0 tr _st_tgt1 -> tr = E0)
      (SRT: exists _st_tgt1, Step L1 st_tgt0 E0 _st_tgt1)
      (SIM: forall st_tgt1
          (STEP: Step L1 st_tgt0 E0 st_tgt1)
        ,
          exists st_src1 (STEP: _.(step) st_src0 None st_src1),
            <<SIM: sim true true st_src1 st_tgt1>>)
    :
      _sim sim f_src f_tgt st_src0 st_tgt0

  (* additional case for partial termination of target *)
  | sim_pterm_tgt
      (SRT: exists _ev_tgt _st_tgt1, Step L1 st_tgt0 [_ev_tgt] _st_tgt1)
      (SRT: forall tr_tgt _st_tgt1, Step L1 st_tgt0 tr_tgt _st_tgt1 -> tr_tgt = [Event_pterm])
    :
      _sim sim f_src f_tgt st_src0 st_tgt0

  | sim_progress
      (SIM: sim false false st_src0 st_tgt0)
      (SRC: f_src = true)
      (TGT: f_tgt = true)
    :
      _sim sim f_src f_tgt st_src0 st_tgt0
  .

  Lemma _sim_ind2
    (r : bool -> bool -> L0.(STS.state) -> L1.(Smallstep.state) -> Prop)
    (P : bool -> bool -> L0.(STS.state) -> L1.(Smallstep.state) -> Prop)
    (RET: forall retv f_src f_tgt st_src0 st_tgt0
            (SRT: _.(state_sort) st_src0 = final retv↑)
            (SRT: _.(Smallstep.final_state) st_tgt0 retv),
            P f_src f_tgt st_src0 st_tgt0 )
    (VIS: forall f_src f_tgt st_src0 st_tgt0
            (SRT: _.(state_sort) st_src0 = vis)
            (NOSILENT: forall _st_tgt1, not (Step L1 st_tgt0 E0 _st_tgt1))
            (TSAFE: exists _ev_tgt _st_tgt1, Step L1 st_tgt0 [_ev_tgt] _st_tgt1)
            (SIM: forall ev_tgt st_tgt1 (STEP: Step L1 st_tgt0 ev_tgt st_tgt1)
                    (NPTERM: ev_tgt <> Some Event_pterm),
                    exists st_src1 ev_src (STEP: _.(step) st_src0 (Some ev_src) st_src1),
                      (<<MATCH: Forall2 (match_event null_map) ev_tgt [ev_src]>>) /\
                      (<<SIM: r true true st_src1 st_tgt1>>)),
            P f_src f_tgt st_src0 st_tgt0)
    (DSRC_STL: forall f_src f_tgt st_src0 st_tgt0
                (SRT: _.(state_sort) st_src0 = demonic)
                (SIM: exists st_src1 (STEP: _.(step) st_src0 None st_src1),
                        <<SIM: _sim r true f_tgt st_src1 st_tgt0>> /\
                        P true f_tgt st_src1 st_tgt0),
                P f_src f_tgt st_src0 st_tgt0)
    (DTGT_STL: forall f_src f_tgt st_src0 st_tgt0
                (NOEVENT: forall tr _st_tgt1, Step L1 st_tgt0 tr _st_tgt1 -> tr = E0)
                (SRT: exists _st_tgt1, Step L1 st_tgt0 E0 _st_tgt1)
                (SIM: forall st_tgt1 (STEP: Step L1 st_tgt0 E0 st_tgt1),
                        <<SIM: _sim r f_src true st_src0 st_tgt1>> /\
                        P f_src true st_src0 st_tgt1),
                P f_src f_tgt st_src0 st_tgt0)
    (ASRC_STL: forall f_src f_tgt st_src0 st_tgt0
                (SRT: _.(state_sort) st_src0 = angelic)
                (DTM: forall st1 st2 (DTM1: _.(step) st_src0 None st1)
                        (DTM2: _.(step) st_src0 None st2), st1 = st2)
                (SIM: forall st_src1 (STEP: _.(step) st_src0 None st_src1),
                        <<SIM: _sim r true f_tgt st_src1 st_tgt0>> /\
                        P true f_tgt st_src1 st_tgt0),
                P f_src f_tgt st_src0 st_tgt0)
    (D_PROG: forall f_src f_tgt st_src0 st_tgt0
                  (NOEVENT: forall tr _st_tgt1, Step L1 st_tgt0 tr _st_tgt1 -> tr = E0)
                  (SRT: exists _st_tgt1, Step L1 st_tgt0 E0 _st_tgt1)
                  (SRT: _.(state_sort) st_src0 = demonic)
                  (SIM: forall st_tgt1 (STEP: Step L1 st_tgt0 E0 st_tgt1),
                        exists st_src1 (STEP: _.(step) st_src0 None st_src1),
                          <<SIM: r true true st_src1 st_tgt1>>),
                P f_src f_tgt st_src0 st_tgt0)
    (PTERM: forall f_src f_tgt st_src0 st_tgt0
            (SRT: exists _ev_tgt _st_tgt1, Step L1 st_tgt0 [_ev_tgt] _st_tgt1)
            (SRT: forall tr_tgt _st_tgt1, Step L1 st_tgt0 tr_tgt _st_tgt1 -> tr_tgt = [Event_pterm]),
            P f_src f_tgt st_src0 st_tgt0 )
    (PROG: forall f_src f_tgt st_src0 st_tgt0
            (SRC: f_src = true)
            (TGT: f_tgt = true)
            (SIM: r false false st_src0 st_tgt0),
            P f_src f_tgt st_src0 st_tgt0)
:
    forall f_src f_tgt st_src st_tgt
           (SIM: _sim r f_src f_tgt st_src st_tgt),
      P f_src f_tgt st_src st_tgt.
  Proof.
    fix IH 5. i. inv SIM.
    { eapply RET; et. }
    { eapply VIS; et. }
    { eapply DSRC_STL; et. des. et. }
    { eapply DTGT_STL; et. i. split; et. apply IH. apply SIM0; et. }
    { eapply ASRC_STL; et. i. exploit SIM0; et. }
    { eapply D_PROG; et. }
    { eapply PTERM; et. }
    { eapply PROG; et. }
  Qed.

  Definition sim: _ -> _ -> _ -> _ -> Prop := paco4 _sim bot4.

  Lemma sim_mon: monotone4 _sim.
  Proof.
    ii. induction IN using _sim_ind2.
    - econs 1; et.
    - econs 2; et. i. exploit SIM; et. i; des. esplits; et.
    - econs 3; et. des. esplits; et.
    - econs 4; et. i. exploit SIM; et. esplits; et. des. et.
    - econs 5; et. i. exploit SIM; et. i. des. et.
    - econs 6; et. des. i. exploit SIM; et. i. des. esplits; et.
    - econs 7; et.
    - econs 8; et.
  Qed.

  Hint Constructors _sim.
  Hint Unfold sim.
  Hint Resolve sim_mon: paco.

  Inductive sim_indC
            (sim: bool -> bool -> state L0 -> Smallstep.state L1 -> Prop)
            (f_src f_tgt: bool) (st_src0: state L0) (st_tgt0: Smallstep.state L1) : Prop :=
  | sim_indC_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv↑)
      (SRT: _.(Smallstep.final_state) st_tgt0 retv)
    :
      sim_indC sim f_src f_tgt st_src0 st_tgt0

  | sim_indC_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: forall _st_tgt1, not (Step L1 st_tgt0 E0 _st_tgt1))
      (SRT: exists _ev_tgt _st_tgt1, Step L1 st_tgt0 [_ev_tgt] _st_tgt1)
      (SIM: forall ev_tgt st_tgt1
          (STEP: Step L1 st_tgt0 ev_tgt st_tgt1)
          (NPTERM: ev_tgt <> Some Event_pterm)
        ,
          exists st_src1 ev_src (STEP: _.(step) st_src0 (Some ev_src) st_src1),
            (<<MATCH: Forall2 (match_event null_map) ev_tgt [ev_src]>>) /\
            (<<SIM: sim true true st_src1 st_tgt1>>))
    :
      sim_indC sim f_src f_tgt st_src0 st_tgt0

  | sim_indC_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: sim true f_tgt st_src1 st_tgt0>>)
    :
      sim_indC sim f_src f_tgt st_src0 st_tgt0

  | sim_indC_demonic_tgt
      (NOEVENT: forall tr _st_tgt1, Step L1 st_tgt0 tr _st_tgt1 -> tr = E0)
      (SRT: exists _st_tgt1, Step L1 st_tgt0 E0 _st_tgt1)
      (SIM: forall st_tgt1
          (STEP: Step L1 st_tgt0 E0 st_tgt1)
        ,
          <<SIM: sim f_src true st_src0 st_tgt1>>)
    :
      sim_indC sim f_src f_tgt st_src0 st_tgt0

  | sim_indC_angelic_src
      (SRT: _.(state_sort) st_src0 = angelic)
      (DTM: forall st1 st2, (<<DTM1: _.(step) st_src0 None st1>>) -> (<<DTM2: _.(step) st_src0 None st2>>) -> st1 = st2)
      (SIM: forall st_src1
          (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: sim true f_tgt st_src1 st_tgt0>>)
    :
      sim_indC sim f_src f_tgt st_src0 st_tgt0

  | sim_indC_demonic_both
      (SRT: _.(state_sort) st_src0 = demonic)
      (NOEVENT: forall tr _st_tgt1, Step L1 st_tgt0 tr _st_tgt1 -> tr = E0)
      (SRT: exists _st_tgt1, Step L1 st_tgt0 E0 _st_tgt1)
      (SIM: forall st_tgt1
          (STEP: Step L1 st_tgt0 E0 st_tgt1)
        ,
          exists st_src1 (STEP: _.(step) st_src0 None st_src1),
            <<SIM: sim true true st_src1 st_tgt1>>)
    :
      sim_indC sim f_src f_tgt st_src0 st_tgt0

  | sim_indC_pterm_tgt
      (SRT: exists _ev_tgt _st_tgt1, Step L1 st_tgt0 [_ev_tgt] _st_tgt1)
      (SRT: forall tr_tgt _st_tgt1, Step L1 st_tgt0 tr_tgt _st_tgt1 -> tr_tgt = [Event_pterm])
    :
      sim_indC sim f_src f_tgt st_src0 st_tgt0
  .

  Lemma sim_indC_mon: monotone4 sim_indC.
  Proof.
    ii. inv IN.
    { econs 1; eauto. }
    { econs 2; eauto. i. hexploit SIM; et. i. des. esplits; eauto. }
    { econs 3; eauto. i. hexploit SIM; et. i. des. esplits; eauto. }
    { econs 4; eauto. i. hexploit SIM; et. }
    { econs 5; eauto. i. hexploit SIM; et. }
    { econs 6; eauto. i. hexploit SIM; et. i. des. esplits; eauto. }
    { econs 7; eauto. }
  Qed.
  Hint Resolve sim_indC_mon: paco.
  Hint Resolve cpn4_wcompat: paco.

  Lemma sim_indC_spec:
    sim_indC <5= gupaco4 _sim (cpn4 _sim).
  Proof.
    eapply wrespect4_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. i. hexploit SIM; et. i. des. esplits; et. eapply rclo4_base. auto. }
    { econs 3; eauto. des. eexists _,_. eapply sim_mon; eauto. i. eapply rclo4_base. auto. }
    { econs 4; eauto. i. hexploit SIM; et. i. eapply sim_mon; eauto. i. eapply rclo4_base. auto. }
    { econs 5; eauto. i. hexploit SIM; et. i. eapply sim_mon; eauto. i. eapply rclo4_base. auto. }
    { econs 6; eauto. i. hexploit SIM; et. i. des. eexists _,_. eapply rclo4_base. eauto. }
    { econs 7; eauto. }
    Unshelve. all: et.
  Qed.

  Lemma sim_ind
    (P : bool -> bool -> L0.(STS.state) -> L1.(Smallstep.state) -> Prop)
    (RET: forall retv f_src f_tgt st_src0 st_tgt0
            (SRT: _.(state_sort) st_src0 = final retv↑)
            (SRT: _.(Smallstep.final_state) st_tgt0 retv),
            P f_src f_tgt st_src0 st_tgt0 )
    (VIS: forall f_src f_tgt st_src0 st_tgt0
            (SRT: _.(state_sort) st_src0 = vis)
            (NOSILENT: forall _st_tgt1, not (Step L1 st_tgt0 E0 _st_tgt1))
            (TSAFE: exists _ev_tgt _st_tgt1, Step L1 st_tgt0 [_ev_tgt] _st_tgt1)
            (SIM: forall ev_tgt st_tgt1 (STEP: Step L1 st_tgt0 ev_tgt st_tgt1)
                    (NPTERM: ev_tgt <> Some Event_pterm),
                    exists st_src1 ev_src (STEP: _.(step) st_src0 (Some ev_src) st_src1),
                      (<<MATCH: Forall2 (match_event null_map) ev_tgt [ev_src]>>) /\
                      (<<SIM: sim true true st_src1 st_tgt1>>)),
            P f_src f_tgt st_src0 st_tgt0)
    (DSRC_STL: forall f_src f_tgt st_src0 st_tgt0
                (SRT: _.(state_sort) st_src0 = demonic)
                (SIM: exists st_src1 (STEP: _.(step) st_src0 None st_src1),
                        <<SIM: sim true f_tgt st_src1 st_tgt0>> /\
                        P true f_tgt st_src1 st_tgt0),
                P f_src f_tgt st_src0 st_tgt0)
    (DTGT_STL: forall f_src f_tgt st_src0 st_tgt0
                (NOEVENT: forall tr _st_tgt1, Step L1 st_tgt0 tr _st_tgt1 -> tr = E0)
                (SRT: exists _st_tgt1, Step L1 st_tgt0 E0 _st_tgt1)
                (SIM: forall st_tgt1 (STEP: Step L1 st_tgt0 E0 st_tgt1),
                        <<SIM: sim f_src true st_src0 st_tgt1>> /\
                        P f_src true st_src0 st_tgt1),
                P f_src f_tgt st_src0 st_tgt0)
    (ASRC_STL: forall f_src f_tgt st_src0 st_tgt0
                (SRT: _.(state_sort) st_src0 = angelic)
                (DTM: forall st1 st2 (DTM1: _.(step) st_src0 None st1)
                        (DTM2: _.(step) st_src0 None st2), st1 = st2)
                (SIM: forall st_src1 (STEP: _.(step) st_src0 None st_src1),
                        <<SIM: sim true f_tgt st_src1 st_tgt0>> /\
                        P true f_tgt st_src1 st_tgt0),
                P f_src f_tgt st_src0 st_tgt0)
    (D_PROG: forall f_src f_tgt st_src0 st_tgt0
                  (NOEVENT: forall tr _st_tgt1, Step L1 st_tgt0 tr _st_tgt1 -> tr = E0)
                  (SRT: exists _st_tgt1, Step L1 st_tgt0 E0 _st_tgt1)
                  (SRT: _.(state_sort) st_src0 = demonic)
                  (SIM: forall st_tgt1 (STEP: Step L1 st_tgt0 E0 st_tgt1),
                        exists st_src1 (STEP: _.(step) st_src0 None st_src1),
                          <<SIM: sim true true st_src1 st_tgt1>>),
                P f_src f_tgt st_src0 st_tgt0)
    (PTERM: forall f_src f_tgt st_src0 st_tgt0
            (SRT: exists _ev_tgt _st_tgt1, Step L1 st_tgt0 [_ev_tgt] _st_tgt1)
            (SRT: forall tr_tgt _st_tgt1, Step L1 st_tgt0 tr_tgt _st_tgt1 -> tr_tgt = [Event_pterm]),
            P f_src f_tgt st_src0 st_tgt0)
    (PROG: forall f_src f_tgt st_src0 st_tgt0
            (SRC: f_src = true)
            (TGT: f_tgt = true)
            (SIM: sim false false st_src0 st_tgt0),
            P f_src f_tgt st_src0 st_tgt0)
:
    forall f_src f_tgt st_src st_tgt
           (SIM: sim f_src f_tgt st_src st_tgt),
      P f_src f_tgt st_src st_tgt.
  Proof.
    i. punfold SIM. induction SIM using _sim_ind2; i; clarify.
    { eapply RET; eauto. }
    { eapply VIS; eauto. i. exploit SIM; eauto. i. des. pclearbot. eauto. }
    { eapply DSRC_STL; eauto. des. esplits; et. }
    { eapply DTGT_STL; eauto. i. exploit SIM; eauto. i. des. auto. }
    { eapply ASRC_STL; eauto. i. exploit SIM; eauto. i. des. auto. }
    { eapply D_PROG; eauto. i. exploit SIM; eauto. i. des. pclearbot. eauto. }
    { eapply PTERM; eauto. }
    { pclearbot. eapply PROG; eauto. }
  Qed.

  Inductive sim_flagC (r: bool -> bool -> state L0 -> Smallstep.state L1 -> Prop) : bool -> bool -> state L0 -> Smallstep.state L1 -> Prop :=
  | flagC_intro
    st_src st_tgt f_src1 f_tgt1 f_src0 f_tgt0
    (SRC: f_src0 = true -> f_src1 = true)
    (TGT: f_tgt0 = true -> f_tgt1 = true)
    (SIM: r f_src0 f_tgt0 st_src st_tgt)
  :
    sim_flagC r f_src1 f_tgt1 st_src st_tgt.

  Lemma sim_flagC_mon
        r1 r2
        (LE: r1 <4= r2)
    :
      sim_flagC r1 <4= sim_flagC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.
  Hint Resolve sim_flagC_mon: paco.

  Lemma sim_flagC_wrespectful: wrespectful4 (_sim) sim_flagC.
  Proof.
    econs; eauto with paco.
    ii. inv PR.
    eapply GF in SIM.
    revert x0 x1 SRC TGT. induction SIM using _sim_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. i. hexploit SIM; et. i. des. esplits; et. eapply rclo4_base. auto. }
    { econs 3; eauto. des. eexists _,_. eapply sim_mon; eauto. }
    { econs 4; eauto. i. hexploit SIM; et. i. des. eapply sim_mon; eauto. }
    { econs 5; eauto. i. hexploit SIM; et. i. des. eapply sim_mon; eauto. }
    { econs 6; eauto. i. hexploit SIM; et. i. des. eexists _,_. eapply rclo4_base. eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. eapply rclo4_clo_base. econs; eauto. }
    Unshelve. all: et.
  Qed.

  Lemma sim_flagC_spec: sim_flagC <5= gupaco4 (_sim) (cpn4 (_sim)).
  Proof.
    intros. eapply wrespect4_uclo; eauto with paco. eapply sim_flagC_wrespectful.
  Qed.

  Lemma sim_flag_down r g st_src st_tgt f_src f_tgt
        (SIM: gpaco4 _sim (cpn4 _sim) r g false false st_src st_tgt)
    :
      gpaco4 _sim (cpn4 _sim) r g f_src f_tgt st_src st_tgt.
  Proof.
    guclo sim_flagC_spec. econs; [..|eauto]; ss.
  Qed.

  Lemma sim_bot_flag_up b0 b1 st_src st_tgt f_src f_tgt
        (SIM: sim b0 b1 st_src st_tgt)
    :
      sim f_src f_tgt st_src st_tgt.
  Proof.
    ginit. revert st_src st_tgt f_src f_tgt b0 b1 SIM.
    gcofix CIH. i. revert f_src f_tgt.
    induction SIM using sim_ind.
    { gstep. econs 1; eauto. }
    { gstep. econs 2; eauto. i. hexploit SIM; et. i. des. esplits; et. gbase. eapply CIH; eauto. }
    { guclo sim_indC_spec. des. econs 3; eauto. }
    { guclo sim_indC_spec. econs 4; et. i. hexploit SIM; et. i. des. et. }
    { guclo sim_indC_spec. econs 5; et. i. hexploit SIM; et. i. des. et. }
    { guclo sim_indC_spec. econs 6; et. i. hexploit SIM; et. i. des. esplits; et. gfinal. right. eapply paco4_mon; et. i. ss. }
    { guclo sim_indC_spec. econs 7; eauto. }
    { i. eapply sim_flag_down. gfinal. right. eapply paco4_mon; eauto. ss. }
  Qed.

  Record simulation: Prop := mk_simulation {
    sim_init: forall st_tgt0 (INITT: L1.(Smallstep.initial_state) st_tgt0),
        (<<SIM: sim false false L0.(initial_state) st_tgt0>>);
    (* sim_init: exists i0 st_tgt0, (<<SIM: sim i0 L0.(initial_state) st_tgt0>>) /\ *)
    (*                              (<<INITT: L1.(Smallstep.initial_state) st_tgt0>>); *)
    (* sim_dtm: True; *)
  }
  .

  (* Hypothesis WF: well_founded ord. *)
  Hypothesis WFSEM: wf_semantics L1.

  Ltac pc H := rr in H; desH H; ss.

  (* no ub along tr *)
  Definition safe_along_events (st_src0: state L0) (tr: list Events.event): Prop := forall
      st_src1
      tx ty tx_src
      (STAR: star L0 st_src0 tx_src st_src1)
      (MB: squeeze (List.map decompile_event tx) = (tx_src, true))
      (PRE: tx ++ ty = tr)
    ,
      <<SAFE: NoStuck L0 st_src1>>
  .

  Definition safe_along_trace (st_src0: state L0) (tr: program_behavior) : Prop := forall
      thd
      (BEH: behavior_prefix thd tr)
    ,
      safe_along_events st_src0 thd
  .

  Lemma match_beh_cons gvmap
        b0 b1
        e0 e1
        b0_ b1_
        (B0_: b0_ = (behavior_app [e0] b0))
        (B1_: b1_ = (Tr.app [e1] b1))
        (M0: match_beh gvmap b0 b1)
        (M1: match_event gvmap e0 e1)
    :
      <<M: match_beh gvmap b0_ b1_>>
  .
  Proof.
    subst.
    revert_until b0. revert b0.
    pcofix CIH. i. punfold M0. inv M0.
    - pfold. econs 1; try refl; ss; et.
    - pfold. econs 2; try refl; ss; et.
    - pfold. econs 3; try refl; ss; et. pclearbot. right.
      change (Reacts (Econsinf ev trinf)) with (behavior_app [ev] (Reacts trinf)).
      eapply CIH; et.
    - pfold. econs 4.
      { instantiate (1:=e1 :: mtr). ss; et. }
      { econs; ss; et. }
      rr in TB. des. subst.
      rr. esplits; ss; et. rewrite <- behavior_app_assoc. ss.
    - pfold. econs 5; ss.
      { econs; et. }
      unfold Tr.prefix in *. des. exists tl. ss. rr. f_equal. et.
  Qed.

  Lemma safe_along_events_step_some
        st_src0 st_src1 e_src e0 es0
        (WFSRC: wf L0 st_src0)
        (STEP: step L0 st_src0 (Some e_src) st_src1)
        (MB: decompile_event e0 = Some e_src)
        (SAFE: safe_along_events st_src0 ([e0] ++ es0))
    :
      <<SAFE: safe_along_events st_src1 es0>>
  .
  Proof.
    ii. des; clarify. eapply SAFE; ss.
    { econs; et. }
    { instantiate (1 := e0 :: _). ss. des_ifs. rewrite MB0 in *; clarify. }
    { ss. }
  Qed.

  Lemma safe_along_events_step_none
        st_src0 st_src1 es0
        (WFSRC: wf L0 st_src0)
        (STEP: step L0 st_src0 None st_src1)
        (SAFE: safe_along_events st_src0 es0)
    :
      <<SAFE: safe_along_events st_src1 es0>>
  .
  Proof.
    ii. des; clarify. eapply SAFE; ss.
    { econs; et. }
    { ss. }
  Qed.

  Lemma safe_along_events_star
        st_src0 st_src1 es0_src es0 es1
        (STAR: star L0 st_src0 es0_src st_src1)
        (MB: squeeze (List.map decompile_event es0) = (es0_src, true))
        (SAFE: safe_along_events st_src0 (es0 ++ es1))
    :
      <<SAFE: safe_along_events st_src1 es1>>
  .
  Proof.
    revert st_src0 st_src1 es0_src es1 STAR MB SAFE. induction es0; ss.
    { i. clarify. ii. subst. exploit SAFE; [..|et|et].
      { instantiate (1:=tx_src).
        change tx_src with ([] ++ tx_src). eapply star_trans; et. }
      { et. }
      { et. }
    }
    { i. des_ifs. ii. subst. exploit SAFE; [..|et|et].
      { instantiate (1:=_ ++ _). eapply star_trans; et. }
      { instantiate (1:=a :: es0 ++ tx). ss. rewrite Heq.
        rewrite List.map_app. rewrite squeeze_app.
        rewrite MB. des_ifs. }
      { instantiate (1:=ty). ss. rewrite ! List.app_assoc. auto. }
    }
  Qed.

  Lemma simulation_star b1 b2
        st_src0 tr_tgt st_tgt1 st_tgt0
        (STEP: Star L1 st_tgt0 tr_tgt st_tgt1)
        (SIM: sim b1 b2 st_src0 st_tgt0)
        (SAFE: safe_along_events st_src0 tr_tgt)
        (NOPTERM: trace_intact tr_tgt)
    :
      exists b1' b2' st_src1 tr_src,
        (<<MB: squeeze (List.map decompile_event tr_tgt) = (tr_src, true)>>) /\
        (<<STEP: star L0 st_src0 tr_src st_src1>>) /\
        (<<SIM: sim b1' b2' st_src1 st_tgt1>>)
  .
  Proof.
    revert SAFE SIM NOPTERM. depgen st_src0. revert b1 b2.
    induction STEP; ii; ss.
    { esplits; et. econs; ss. }
    subst. rename s1 into st_tgt0. rename s2 into st_tgt1. rename s3 into st_tgt2.
    rename t1 into tr_tgt0. rename t2 into tr_tgt1.
    punfold SIM.
    induction SIM using _sim_ind2.
    - (* fin *)
      exploit wf_at_final; [apply WFSEM|..]; et. ss.
    - (* vis *)
      destruct (classic (tr_tgt0 = Some Event_pterm)).
      { exfalso. subst. apply NOPTERM. ss. et. }
      rename H0 into D.
      exploit SIM; et. i; des. pclearbot.
      inv MATCH; ss. inv H4; ss. rename H3 into MB.
      eapply match_event_iff in MB. des_ifs.
      exploit IHSTEP; et.
      { eapply safe_along_events_step_some; et. unfold wf. i. rewrite ANG in SRT. ss. }
      { red. red. i. apply NOPTERM. ss. et. }
      i; des. clarify.
      esplits; et. rewrite cons_app.
      change [ev_src] with (option_to_list (Some ev_src)).
      econs; et.
      unfold wf. i. rewrite ANG in SRT. ss.
    - (* dsrc *)
      des. pclearbot. hexploit SIM1; et.
      { eapply safe_along_events_step_none; et. unfold wf. i. rewrite ANG in SRT. ss. }
      i; des.
      esplits; et.
      rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. rewrite ANG in SRT. ss.
    - (* dtgt *)
      des. pclearbot. exploit NOEVENT. apply H. i. subst.
      exploit SIM. apply H. i. des.
      exploit IHSTEP; et.
    - (* asrc *)
      exploit SAFE; try apply SRT.
      { econs; et. }
      { instantiate (1:=[]). ss. }
      { ss. }
      i; des.
      exploit wf_angelic; et. i; subst.
      exploit SIM; et. i; des. pclearbot.
      exploit x2; et.
      { eapply safe_along_events_step_none; et. unfold wf. i. apply DTM; eauto. }
      i; des.
      esplits; et.
      rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. apply DTM; eauto.
    - (* dboth *)
      des. pclearbot.
      exploit NOEVENT. apply H. i. subst.
      exploit SIM. apply H. i. des. pclearbot.
      exploit IHSTEP.
      { eapply safe_along_events_step_none; et. unfold wf. i. rewrite ANG in SRT0. ss. }
      all: et.
      i; des.
      esplits; et. rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. rewrite ANG in SRT0. ss.
    - (* pterm *)
      des. apply SRT0 in H. subst. ss. exfalso. apply NOPTERM. ss. et.
    - pclearbot. punfold SIM. clear SRC TGT f_src f_tgt.
      set false as b1 in SIM at 1. set false as b2 in SIM.
      assert (E2: b2 = false) by et.
      clearbody b1 b2.
      induction SIM using _sim_ind2.
    + (* fin *)
      exploit wf_at_final; [apply WFSEM|..]; et. ss.
    + (* vis *)
      destruct (classic (tr_tgt0 = Some Event_pterm)).
      { exfalso. subst. apply NOPTERM. ss. et. }
      rename H0 into D.
      exploit SIM; et. i; des. pclearbot.
      inv MATCH; ss. inv H4; ss. rename H3 into MB. eapply match_event_iff in MB. des_ifs.
      exploit IHSTEP; et.
      { eapply safe_along_events_step_some; et. unfold wf. i. rewrite ANG in SRT. ss. }
      { red. red. i. apply NOPTERM. ss. et. }
      i; des. clarify.
      esplits; et. rewrite cons_app.
      change [ev_src] with (option_to_list (Some ev_src)).
      econs; et.
      unfold wf. i. rewrite ANG in SRT. ss.
    + (* dsrc *)
      des. pclearbot. hexploit SIM1; et.
      { eapply safe_along_events_step_none; et. unfold wf. i. rewrite ANG in SRT. ss. }
      i; des.
      esplits; et.
      rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. rewrite ANG in SRT. ss.
    + (* dtgt *)
      des. pclearbot.
      exploit NOEVENT. apply H. i. subst.
      exploit SIM. apply H. i. des.
      exploit IHSTEP; et.
    + (* asrc *)
      exploit SAFE; try apply SRT.
      { econs; et. }
      { instantiate (1:=[]). ss. }
      { ss. }
      i; des.
      exploit wf_angelic; et. i; subst.
      exploit SIM; et. i; des. pclearbot.
      exploit x2; et.
      { eapply safe_along_events_step_none; et. unfold wf. i. apply DTM; eauto. }
      i; des.
      esplits; et.
      rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. apply DTM; eauto.
    + (* dboth *)
      des. pclearbot.
      exploit NOEVENT. apply H. i. subst.
      exploit SIM. apply H. i. des. pclearbot.
      exploit IHSTEP.
      { eapply safe_along_events_step_none; et. unfold wf. i. rewrite ANG in SRT0. ss. }
      all: et.
      i; des.
      esplits; et. rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. rewrite ANG in SRT0. ss.
    + (* pterm *)
      des. apply SRT0 in H. subst. ss. exfalso. apply NOPTERM. ss. et.
    + clarify.
  Qed.

  Lemma simulation_star_nonintact b1 b2
        st_src0 tr_tgt st_tgt1 st_tgt0
        (STEP: Star L1 st_tgt0 tr_tgt st_tgt1)
        (SIM: sim b1 b2 st_src0 st_tgt0)
        (SAFE: safe_along_trace st_src0 (Partial_terminates (trace_cut_pterm tr_tgt)))
        (PTERM: ~ trace_intact tr_tgt)
    :
      exists st_src1 tr_src,
        (<<MB: squeeze (List.map decompile_event (trace_cut_pterm tr_tgt)) = (tr_src, true)>>) /\
        (<<STEP: star L0 st_src0 tr_src st_src1>>)
  .
  Proof.
    revert SAFE SIM PTERM. depgen st_src0. revert b1 b2.
    induction STEP; ii; ss.
    { esplits; et. econs; ss. }
    subst. rename s1 into st_tgt0. rename s2 into st_tgt1. rename s3 into st_tgt2.
    rename t1 into tr_tgt0. rename t2 into tr_tgt1.
    punfold SIM.
    induction SIM using _sim_ind2.
    - (* fin *)
      exploit wf_at_final; [apply WFSEM|..]; et. ss.
    - (* vis *)
      destruct (classic (tr_tgt0 = Some Event_pterm)).
      { subst. ss. exists st_src0, []. split; et. econs. }
      rename H0 into D.
      exploit SIM; et. i; des. pclearbot.
      inv MATCH; ss. inv H4; ss. rename H3 into MB. eapply match_event_iff in MB. des_ifs.
      unfold safe_along_trace in *.
      exploit IHSTEP; et.
      { i. eapply safe_along_events_step_some; et.
        2:{ apply SAFE. unfold behavior_prefix in *. des. exists beh'.
            rewrite behavior_app_assoc. rewrite <- BEH. ss. }
        unfold wf. i. rewrite ANG in SRT. ss. }
      { red. i. apply PTERM. unfold trace_intact in *. red. i. apply H0. ss. des; clarify. }
      i; des.
      esplits; et.
      2:{ econs 2; et. unfold wf. i. rewrite ANG in SRT. ss. }
      change (map _ _) with ((decompile_event (Event_syscall s l e)) :: (map decompile_event (trace_cut_pterm tr_tgt1))).
      rewrite MB. ss. des_ifs.
    - (* dsrc *)
      des. pclearbot. hexploit SIM1; et.
      { unfold safe_along_trace. i. eapply safe_along_events_step_none; et. unfold wf. i. rewrite ANG in SRT. ss. }
      i; des.
      esplits; et.
      rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. rewrite ANG in SRT. ss.
    - (* dtgt *)
      des. exploit NOEVENT. apply H. i. subst.
      exploit SIM. apply H. i. des.
      exploit IHSTEP; et.
    - (* asrc *)
      exploit SAFE; try apply SRT.
      { instantiate (1:=[]). eexists (Partial_terminates _). ss. }
      { econs; et. }
      { instantiate (1:=[]). ss. }
      { ss. }
      i; des.
      exploit wf_angelic; et. i; subst.
      exploit SIM; et. i; des. pclearbot.
      exploit x2; et.
      { unfold safe_along_trace. i. eapply safe_along_events_step_none; et. unfold wf. i. apply DTM; eauto. }
      i; des.
      esplits; et.
      rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. apply DTM; eauto.
    - (* dboth *)
      des. exploit NOEVENT. apply H. i. subst.
      exploit SIM. apply H. i. des. pclearbot.
      exploit IHSTEP;[|et|et|].
      { unfold safe_along_trace. i. eapply safe_along_events_step_none; et. unfold wf. i. rewrite ANG in SRT0. ss. }
      i; des.
      esplits; et. rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. rewrite ANG in SRT0. ss.
    - (* pterm *)
      hexploit SRT0; et. i. subst. ss. exists st_src0, [].
      split; et. econs.
    - pclearbot. punfold SIM. clear SRC TGT f_src f_tgt.
      set false as b1 in SIM at 1. set false as b2 in SIM.
      assert (E2: b2 = false) by et.
      clearbody b1 b2.
      induction SIM using _sim_ind2.
    + (* fin *)
      exploit wf_at_final; [apply WFSEM|..]; et. ss.
    + (* vis *)
      destruct (classic (tr_tgt0 = Some Event_pterm)).
      { subst. ss. exists st_src0, []. split; et. econs. }
      rename H0 into D.
      exploit SIM; et. i; des. pclearbot.
      inv MATCH; ss. inv H4; ss. rename H3 into MB. eapply match_event_iff in MB. des_ifs.
      unfold safe_along_trace in *.
      exploit IHSTEP; et.
      { i. eapply safe_along_events_step_some; et.
        2:{ apply SAFE. unfold behavior_prefix in *. des. exists beh'.
            rewrite behavior_app_assoc. rewrite <- BEH. ss. }
        unfold wf. i. rewrite ANG in SRT. ss. }
      { red. i. apply PTERM. unfold trace_intact in *. red. i. apply H0. ss. des; clarify. }
      i; des.
      esplits; et.
      2:{ econs 2; et. unfold wf. i. rewrite ANG in SRT. ss. }
      change (map _ _) with ((decompile_event (Event_syscall s l e)) :: (map decompile_event (trace_cut_pterm tr_tgt1))).
      rewrite MB. ss. des_ifs.
    + (* dsrc *)
      des. pclearbot. hexploit SIM1; et.
      { unfold safe_along_trace. i. eapply safe_along_events_step_none; et. unfold wf. i. rewrite ANG in SRT. ss. }
      i; des.
      esplits; et.
      rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. rewrite ANG in SRT. ss.
    + (* dtgt *)
      des. exploit NOEVENT. apply H. i. subst.
      exploit SIM. apply H. i. des.
      exploit IHSTEP; et.
    + (* asrc *)
      exploit SAFE; try apply SRT.
      { instantiate (1:=[]). eexists (Partial_terminates _). ss. }
      { econs; et. }
      { instantiate (1:=[]). ss. }
      { ss. }
      i; des.
      exploit wf_angelic; et. i; subst.
      exploit SIM; et. i; des. pclearbot.
      exploit x2; et.
      { unfold safe_along_trace. i. eapply safe_along_events_step_none; et. unfold wf. i. apply DTM; eauto. }
      i; des.
      esplits; et.
      rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. apply DTM; eauto.
    + (* dboth *)
      des. exploit NOEVENT. apply H. i. subst.
      exploit SIM. apply H. i. des. pclearbot.
      exploit IHSTEP;[|et|et|].
      { unfold safe_along_trace. i. eapply safe_along_events_step_none; et. unfold wf. i. rewrite ANG in SRT0. ss. }
      i; des.
      esplits; et. rewrite <- (app_nil_l tr_src).
      change [] with (@option_to_list event None).
      econs; et.
      unfold wf. i. rewrite ANG in SRT0. ss.
    + (* pterm *)
      hexploit SRT0; et. i. subst. ss. exists st_src0, [].
      split; et. econs.
    + clarify.
  Qed.

  Lemma sim_forever_silent
        b1 b2 st_src st_tgt
        (SIM: sim b1 b2 st_src st_tgt)
        (SILENT: Forever_silent L1 st_tgt)
    :
      Beh.state_spin L0 st_src.
  Proof.
    revert b1 b2 st_src st_tgt SIM SILENT. pcofix CIH.
    i. inv SILENT. punfold SIM. depgen s2. induction SIM using _sim_ind2; i.
    { exploit wf_at_final; [apply WFSEM|..]; et. ss. }
    { des. exfalso. eapply NOSILENT. et. }
    { des. hexploit SIM1; et. i. pfold. econs 2; et. esplits; et. }
    { des. inv H0. eapply SIM; et. }
    { pfold. econs 1; et. i.
      hexploit wf_angelic; et. i. subst.
      hexploit SIM; et. i. des. left. eapply H2; et. }
    { des. hexploit SIM. apply H. i. des.
      pclearbot. pfold. econs 2; et. esplits; et. }
    { des. apply SRT0 in H. clarify. }
    { pclearbot. clear SRC TGT f_src f_tgt.
      remember false as b1 in SIM at 1. set false as b2 in SIM. clearbody b2.
      punfold SIM. depgen s2. induction SIM using _sim_ind2; i.
    { exploit wf_at_final; [apply WFSEM|..]; et. ss. }
    { des. apply NOSILENT in H. clarify. }
    { des. i. pfold. econs 2; et. esplits; et. right. eapply CIH; et. econs; et. }
    { des. inv H0. eapply SIM; et. }
    { pfold. econs 1; et. i.
      hexploit wf_angelic; et. i. subst.
      hexploit SIM; et. i. des. right. eapply CIH; et. econs; et. }
    { des. hexploit SIM. apply H. i. des.
      pclearbot. pfold. econs 2; et. esplits; et. }
    { des. apply SRT0 in H. clarify. }
    clarify. }
  Qed.


  Lemma sim_goes_wrong
        b1 b2 st_src st_tgt
        (SIM: sim b1 b2 st_src st_tgt)
        (NOSTEP: Nostep L1 st_tgt)
        (NOFINAL: forall r, ~ L1.(Smallstep.final_state) st_tgt r)
    :
      Beh.of_state L0 st_src Tr.ub.
  Proof.
    ginit.
    i. punfold SIM. induction SIM using _sim_ind2; ss.
    { exfalso. eapply NOFINAL; et. }
    { des. exfalso. eapply NOSTEP; et. }
    { des. hexploit SIM1; ss. i.
      guclo starC_spec. econs; et.
      change ([]: list event) with (None ++ []: list event). econs; et.
      unfold wf; i. rewrite ANG in SRT; ss. }
    { des. exfalso. eapply NOSTEP; et. }
    { gstep. econs 6; et. unfold Beh.inter. i.
      hexploit wf_angelic; et. i. subst. split; et.
      hexploit SIM; et. i. des. red. apply gpaco2_unfold_bot.
      { apply Beh.of_state_mon. }
      { eapply cpn2_wcompat. eapply Beh.of_state_mon. }
      et. }
    { des. exfalso. eapply NOSTEP; et. }
    { des. exfalso. eapply NOSTEP; et. }
    { pclearbot. clear SRC TGT f_src f_tgt.
      remember false as b2 in SIM at 2. set false as b1 in SIM. clearbody b1.
      punfold SIM. induction SIM using _sim_ind2; i.
    { exfalso. eapply NOFINAL; et. }
    { des. exfalso. eapply NOSTEP; et. }
    { des. hexploit SIM1; ss. i.
      guclo starC_spec. econs; et.
      change ([]: list event) with (None ++ []: list event). econs; et.
      unfold wf; i. rewrite ANG in SRT; ss. }
    { des. exfalso. eapply NOSTEP; et. }
    { gstep. econs 6; et. unfold Beh.inter. i.
      hexploit wf_angelic; et. i. subst. split; et.
      hexploit SIM; et. i. des. red. apply gpaco2_unfold_bot.
      { apply Beh.of_state_mon. }
      { eapply cpn2_wcompat. eapply Beh.of_state_mon. }
      et. }
    { des. exfalso. eapply NOSTEP; et. }
    { des. exfalso. eapply NOSTEP; et. }
    clarify. }
  Qed.

  Lemma adequacy_aux
        st_src0 st_tgt0
        (SIM: sim false false st_src0 st_tgt0)
    :
      <<IMPR: improves2 null_map st_src0 st_tgt0>>
  .
  Proof.
    ii.
    (* set (transl_beh tr_tgt) as tr_src in *. *)
    destruct (classic (safe_along_trace st_src0 tr_tgt)); rename H into SAFE.
    { (*** safe ***)
      exists (transl_beh tr_tgt).
      inv BEH.
      - (rename t into tr; rename H into STAR; rename s' into st_tgt1; rename H0 into FIN).
        esplits; et.
        + ss. des_ifs_safe.
          hexploit simulation_star; try apply STAR; et.
          { eapply SAFE. exists (Terminates [] r). ss. unfold Eapp. rewrite app_nil_r; ss. }
          i; des.
          rewrite MB in *. clarify.


          (*** 1. : star + Beh.of_state -> Beh.of_state app ***)
          eapply beh_of_state_star; ss; et.
          cut (Beh.of_state L0 st_src1 (Tr.done r↑)); ss.
          (* assert(SAFE0: safe_along_trace st_src1 (Terminates tr r)). *)
          assert(SAFE0: safe_along_events st_src1 []).
          { clear - SAFE STEP MB.
            r in SAFE. specialize (SAFE tr).
            hexploit1 SAFE.
            { eexists (Terminates nil _). ss. unfold Eapp. rewrite List.app_nil_r. ss. }
            eapply safe_along_events_star; et.
            rewrite List.app_nil_r. ss.
          }
          clear - SAFE0 FIN SIM0 WFSEM.
          i. punfold SIM0. induction SIM0 using _sim_ind2; ss.
          * pfold. econs; ss; et.
            exploit wf_at_final_determ; [eapply WFSEM|eapply SRT0|eapply FIN|].
            i. des. clarify.
          * des. exploit wf_at_final; [apply WFSEM|..]; et. ss.
          * des. eapply Beh.beh_dstep; ss; et.
            eapply SIM1; et.
            eapply safe_along_events_step_none; et. unfold wf; i.
            rewrite ANG in SRT; ss.
          * des. exploit wf_at_final; [apply WFSEM|..]; et. ss.
          * pfold. econs 6; et. red. i.
            hexploit wf_angelic; et. i. subst. split; et.
            hexploit SIM; et. i. des. red. pfold_reverse.
            eapply H0; et.
            eapply safe_along_events_step_none; et. unfold wf; i. eapply DTM; eauto.
          * des. exploit wf_at_final; [apply WFSEM|..]; et. ss.
          * des. exploit wf_at_final; [apply WFSEM|..]; et. ss.
          * pclearbot. clear SRC TGT f_src f_tgt.
            remember false as b2 in SIM at 2. set false as b1 in SIM. clearbody b1.
            punfold SIM. induction SIM using _sim_ind2; i.
          ** pfold. econs; ss; et.
            exploit wf_at_final_determ; [eapply WFSEM|eapply SRT0|eapply FIN|].
            i. des. clarify.
          ** des. exploit wf_at_final; [apply WFSEM|..]; et. ss.
          ** des. eapply Beh.beh_dstep; ss; et.
            eapply SIM1; et.
            eapply safe_along_events_step_none; et. unfold wf; i.
            rewrite ANG in SRT; ss.
          ** des. exploit wf_at_final; [apply WFSEM|..]; et. ss.
          ** pfold. econs 6; et. red. i.
            hexploit wf_angelic; et. i. subst. split; et.
            hexploit SIM; et. i. des. red. pfold_reverse.
            eapply H0; et.
            eapply safe_along_events_step_none; et. unfold wf; i. eapply DTM; eauto.
          ** des. exploit wf_at_final; [apply WFSEM|..]; et. ss.
          ** des. exploit wf_at_final; [apply WFSEM|..]; et. ss.
          ** clarify.
        + ss. clear.
          induction tr; ii; ss.
          { pfold. econs; ss; et. }
          destruct (decompile_event a) eqn:T.
          * des_ifs_safe.
            eapply match_beh_cons; ss.
            { instantiate (1:=Terminates tr r). instantiate (1:=a). ss. }
            { ss. }
            { eapply decompile_match_event; ss. }
          * des_ifs_safe. ss. pfold; econs 4; et; ss. r. esplits; et.
            rewrite behavior_app_E0; et.
      - ss. esplits.
        + ss. des_ifs_safe.
          hexploit simulation_star_nonintact; et.
          i; des.
          rewrite MB in *. clarify.
          eapply beh_of_state_star; ss; et.
        + ss. clear.
          set (trace_cut_pterm t) as t' in *. clearbody t'.
          induction t'; ii; ss.
          { pfold. econs 5; ss; et. red. exists Tr.nb. red. et. }
          destruct (decompile_event a) eqn:T.
          * des_ifs_safe.
            eapply match_beh_cons; ss.
            { instantiate (1:=Partial_terminates t'). instantiate (1:=a). ss. }
            { ss. }
            { eapply decompile_match_event; ss. }
          * des_ifs_safe. ss. pfold; econs 4; et; ss. r. esplits; et.
            rewrite behavior_app_E0; et.
      - (* diverge *)
        (rename t into tr).
        esplits; et.
        + rename H0 into BEH. ss.
          ginit.  revert_until WFSEM. gcofix CIH. i.
          inv BEH.
          rename s2 into st_tgt1. rename tr into tr_tgt. rename H into STAR.
          hexploit simulation_star; try apply STAR; et.
          { eapply SAFE. exists (Diverges []). ss. rewrite E0_right. auto. }
          i; des.
          rewrite MB.
          guclo starC2_spec. econs; et.
          gfinal. right. pfold. econs 2.
          eapply sim_forever_silent; et. econs; et.
        + ss. clear.
          induction tr; ii; ss.
          { pfold. econs 2; ss; et. }
          destruct (decompile_event a) eqn:T.
          * des_ifs_safe.
            eapply match_beh_cons; ss.
            { instantiate (1:=Diverges tr). instantiate (1:=a). ss. }
            { ss. }
            { eapply decompile_match_event; ss. }
          * des_ifs_safe. ss. pfold; econs 4; et; ss. r. esplits; et.
            rewrite behavior_app_E0; et.

      - (* forever_reactive *)
        (rename T into tr).
        esplits; et.
        + rename H into BEH. ss.
          ginit.
          set false as b1 in SIM at 1. set false as b2 in SIM.
          clearbody b1 b2.
          revert_until WFSEM. gcofix CIH. i.
          (* revert_until WFSRC. pcofix CIH. i. *)
          inv BEH.
          rename s2 into st_tgt1. rename t into tr_tgt. rename H into STAR.
          hexploit simulation_star; try apply STAR; et.
          { eapply SAFE. exists (Reacts T). ss. }
          i; des.

          erewrite decompile_trinf_app; et.

          exploit CIH; et.
          { clear - SAFE MB STEP. r. i. eapply safe_along_events_star; et.
            eapply SAFE. r in BEH. des. r. exists beh'. rewrite behavior_app_assoc.
            rewrite <- BEH. ss. }
          intro KNOWLEDGE.
          assert(PROG: tr_src <> []).
          { ii; subst; ss. destruct tr_tgt; ss. des_ifs. }
          clear - KNOWLEDGE PROG STEP.
          induction STEP using star_event_ind; ss.
          clear_tac. spc IHSTEP1.
          eapply star_single_exact in STEP1. des.
          guclo starC_spec. econs; et.
          gstep. econs; et.
          { destruct (state_sort L0 st3) eqn:SORT; auto.
            - exfalso. hexploit wf_angelic; et; ss.
            - exfalso. hexploit wf_demonic; et; ss.
            - exfalso. hexploit wf_final; et; ss.
          }
          guclo starC_spec. econs; et.
          destruct es; ss.
          * guclo starC_spec. econs; et. gbase. et.
          * exploit IHSTEP1; ss; et. intro U. eapply gpaco2_mon; et. ii; ss.
        + eapply decompile_trinf_spec.

      - (* goes wrong *)
        (rename t into tr).
        esplits; et.
        + rename H0 into BEH. ss.
          ginit. revert_until WFSEM. gcofix CIH. i.
          hexploit simulation_star; try apply STAR; et.
          { eapply SAFE. exists (Goes_wrong []). ss. rewrite E0_right. auto. }
          i; des.
          rewrite MB.
          guclo starC2_spec. econs; et.
          gfinal. right. eapply paco2_mon.
          { eapply sim_goes_wrong; et. }
          { ss. }
        + ss. clear.
          induction tr; ii; ss.
          { pfold. econs 4; ss; et. ss. exists (Goes_wrong []). ss. }
          destruct (decompile_event a) eqn:T.
          * des_ifs_safe.
            eapply match_beh_cons; ss.
            { instantiate (1:=Goes_wrong tr). instantiate (1:=a). ss. }
            { ss. }
            { eapply decompile_match_event; ss. }
          * des_ifs_safe. ss. pfold; econs 4; et; ss. r. esplits; et.
            rewrite behavior_app_E0; et.
    }
    { (*** unsafe ***)
      assert(NOTSAFE:
               exists st_src1 thd thd_tgt,
                 (<<B: behavior_prefix thd_tgt tr_tgt>>)
                 /\ (<<MB: squeeze (List.map decompile_event thd_tgt) = (thd, true)>>)
                 /\ (<<STAR: star L0 st_src0 thd st_src1>>)
                 /\ (<<STUCK: ~NoStuck L0 st_src1>>)).
      { unfold safe_along_trace in SAFE. Psimpl. des.
        unfold safe_along_events in *. Psimpl. des.
        Psimpl. des. Psimpl. des.
        subst.
        esplits; try apply SAFE1; ss; et.
        clear - SAFE.
        r in SAFE. des; subst. r. eexists (behavior_app _ _).
        rewrite <- behavior_app_assoc. ss; et.
      }
      des.
      exists (Tr.app thd Tr.ub). esplits; ss.
      - clear - STAR STUCK.
        eapply beh_of_state_star; et. unfold NoStuck in *.
        repeat (Psimpl; des; unfold NW in * ). clears st_src0. clear st_src0.
        pfold. econsr; ss; et. ii. exploit wf_angelic; ss; et. i; subst. exfalso.
        exploit STUCK0; ss; et.
      - r in B. des. subst. clear - MB.
        ginduction thd_tgt; ii; ss; clarify.
        { ss. pfold. econs 4; ss; et.
          { r. esplits; ss; et. }
        }
        des_ifs. ss.
        eapply match_event_iff in Heq.
        eapply match_beh_cons; ss; et. rewrite <- behavior_app_assoc. ss.
    }
  Qed.

  Lemma adequacy gvmap
        st_src0 st_tgt0
        (SIM: sim false false st_src0 st_tgt0)
    :
      <<IMPR: improves2 gvmap st_src0 st_tgt0>>
  .
  Proof. eapply improves2_map_mon; cycle 1. apply adequacy_aux; et. ii. ss. Qed.

End SIM.
Hint Constructors _sim.
Hint Unfold sim.
Hint Resolve sim_mon: paco.
