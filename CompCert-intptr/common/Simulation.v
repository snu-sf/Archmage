Require Export Smallstep.
Require Import Values.
Require Import Globalenvs.
Require Import Memory.
Require Import Integers.
Require Import Events.
Require Import AST.
From Paco Require Import paco.
Require Import sflib.
Require Import CoqlibC.
Require Import Axioms.
Require Import Relations.
Require Import Wellfounded.
Require Import Program.Equality.

Set Implicit Arguments.



(**********************************************************************************************************)
(**********************************************************************************************************)
(**********************************************************************************************************)

Lemma well_founded_clos_trans
      index
      (order: index -> index -> Prop)
      (WF: well_founded order):
    <<WF: well_founded (clos_trans index order)>>.
Proof.
  hnf in WF. hnf. i. eapply Acc_clos_trans. eauto.
Qed.

Lemma clos_t_rt:
  forall (A : Type) (R : relation A) (x y z : A),
  clos_trans A R x y -> clos_refl_trans A R y z -> clos_trans A R x z.
Proof.
  i. induction H0; ss.
  - eapply t_trans; eauto.
  - eapply IHclos_refl_trans2; eauto.
Qed.

Definition gm_improves (gm1 gm2: positive -> option Z) :=
  forall id z, gm1 id = Some z -> gm2 id = Some z.

Definition tr_improves ev_rel1 ev_rel2 :=
  @tr_rel ev_rel1 <2= @tr_rel ev_rel2.

Lemma evval_rel_eq ev:
  evval_rel (fun _  => None) ev ev.
Proof. destruct ev; ss. Qed.

Lemma evval_list_rel_eq ev:
  Forall2 (evval_rel (fun _  => None)) ev ev.
Proof. ginduction ev; ss. econs; eauto. eapply evval_rel_eq. Qed.

Lemma ev_rel_eq ev:
  ev_rel (fun _  => None) ev ev.
Proof.
  destruct ev; ss; esplits; eauto; try by eapply evval_rel_eq.
  - eapply evval_list_rel_eq.
  - eapply evval_list_rel_eq.
Qed.

Lemma tr_rel_eq tr :
  tr_rel (ev_rel (fun _ => None)) tr tr.
Proof. ginduction tr; ss; econs; eauto; ss. eapply ev_rel_eq. Qed.

Lemma evval_rel_refl pm ev:
  evval_rel pm ev ev.
Proof. destruct ev; ss. Qed.

Lemma evval_list_rel_refl pm ev:
  Forall2 (evval_rel pm) ev ev.
Proof. ginduction ev; ss. econs; eauto. eapply evval_rel_refl. Qed.

Lemma tr_rel_div_r ev_rel t t1 t2
    (TRREL: tr_rel ev_rel t (t1 ** t2)):
  exists t1' t2', t = t1' ** t2' /\
             tr_rel ev_rel t1' t1 /\
             tr_rel ev_rel t2' t2.
Proof.
  ginduction t1; ss; ii.
  { exists E0, t. esplits; eauto. econs. }
  inv TRREL. exploit IHt1; eauto. i. des. subst.
  exists (x::t1'), t2'. esplits; eauto. econs; eauto.
Qed.

Lemma tr_rel_div_l ev_rel t t1 t2
    (TRREL: tr_rel ev_rel (t1 ** t2) t):
  exists t1' t2', t = t1' ** t2' /\
             tr_rel ev_rel t1 t1' /\
             tr_rel ev_rel t2 t2'.
Proof.
  ginduction t1; ss; ii.
  { exists E0, t. esplits; eauto. econs. }
  inv TRREL. exploit IHt1; eauto. i. des. subst.
  exists (y::t1'), t2'. esplits; eauto. econs; eauto.
Qed.

(**********************************************************************************************************)
(**********************************************************************************************************)
(**********************************************************************************************************)

Module NOSTUTTER.

Section BACKWARD_SIM.

  Variables L1 L2: semantics.
  
  Variable gvmap : ident -> option Z. (* initial map *)

  Variable index: Type.
  Variable order: index -> index -> Prop.

  Variant bsim_step bsim (i0: index) (st_src0: L1.(state)) (st_tgt0: L2.(state)) : Prop :=
  | bsim_step_step
      (STEP: forall tr' st_tgt1
               (STEPTGT: Step L2 st_tgt0 tr' st_tgt1),
             (exists st_src1 tr i1,
                <<TREL: tr_rel (ev_rel gvmap) tr tr'>> /\
                (<<PLUS: Plus L1 st_src0 tr st_src1>> \/ <<STAR: Star L1 st_src0 tr st_src1 /\ order i1 i0>>) /\
                <<BSIM: bsim i1 st_src1 st_tgt1>>)
             \/
             (exists st_src1 tr,
              <<PTERM: ~ trace_intact tr' >> /\
              <<STAR: Star L1 st_src0 tr st_src1>> /\ 
              <<TREL: exists tl, tr_rel (ev_rel gvmap) tr ((trace_cut_pterm tr') ** tl)>>))
      (FINAL: forall retv
                (FINALTGT: final_state L2 st_tgt0 retv),
              exists st_src1,
              <<STEPSRC: Star L1 st_src0 E0 st_src1>> /\
              <<FINALSRC: final_state L1 st_src1 retv>>)
      (PROGRESS: <<FINAL: exists retv, final_state L2 st_tgt0 retv>> \/
                 <<STEP: exists tr st', Step L2 st_tgt0 tr st'>>).

  Variant _bsim bsim (i0: index) (st_src0: state L1) (st_tgt0: state L2): Prop :=
  | bsim_intro
      (STEP: forall
            (SAFESRC: safe L1 st_src0),
          <<STEP: bsim_step bsim i0 st_src0 st_tgt0>>).

  Definition bsim: _ -> _ -> _ -> Prop := paco3 _bsim bot3.

  Lemma bsim_mon: monotone3 _bsim.
  Proof.
    ii. inv IN. econs; eauto. i. exploit STEP; eauto. i; des_safe. inv H.
    - econs; eauto. i. exploit STEP0; eauto.
      i. destruct H; des_safe.
      + left; esplits; eauto.
      + right. esplits; eauto.
  Qed.

End BACKWARD_SIM.

Hint Unfold bsim.
Hint Resolve bsim_mon: paco.

Record bsim_properties (L1 L2: semantics)
   (index: Type) (order: index -> index -> Prop) : Prop := {
    bsim_order_wf: <<WF: well_founded order>>;
    bsim_initial_states_exist: forall st_init_src
        (INITSRC: initial_state L1 st_init_src),
        exists st_init_tgt, <<INITTGT: initial_state L2 st_init_tgt>>;
    bsim_match_initial_states: forall st_init_src_
        (INITSRC: initial_state L1 st_init_src_)
        st_init_tgt
        (INITTGT: initial_state L2 st_init_tgt)
        st_init_tgt1
        (TGTCAP: initial_capture L2 st_init_tgt st_init_tgt1)
        gmtgt
        (GVMAPTGT: initial_pimap L2 st_init_tgt1 = gmtgt),
      exists i0 st_init_src st_init_src1 gmsrc,
      <<INITSRC: initial_state L1 st_init_src>> /\
      <<SRCCAP: initial_capture L1 st_init_src st_init_src1>> /\
      <<GVMAPSRC: initial_pimap L1 st_init_src1 = gmsrc>> /\
      <<GMSUB: gm_improves gmsrc gmtgt>> /\                                                          
      <<BSIM: @bsim L1 L2 gmtgt index order i0 st_init_src1 st_init_tgt1>>;
}.

Arguments bsim_properties: clear implicits.

Variant backward_simulation (L1 L2: semantics): Prop :=
  Backward_simulation (index: Type)
                      (order: index -> index -> Prop)
                      (props: bsim_properties L1 L2 index order).

Arguments Backward_simulation {L1 L2 index} order props.

End NOSTUTTER.


Section BACKWARD_SIM.

  Variables L1 L2: semantics.
  
  Variable gvmap : ident -> option Z.  (* Initial map *)

  Variable index: Type.
  Variable order: index -> index -> Prop.

  Variant bsim_step bsim (i0: index) (st_src0: L1.(state)) (st_tgt0: L2.(state)) : Prop :=
  | bsim_step_step
      (STEP: forall tr' st_tgt1
               (STEPTGT: Step L2 st_tgt0 tr' st_tgt1),
             (exists st_src1 tr i1,
                <<TREL: tr_rel (ev_rel gvmap) tr tr'>> /\
                (<<PLUS: Plus L1 st_src0 tr st_src1>> \/ <<STAR: Star L1 st_src0 tr st_src1 /\ order i1 i0>>) /\
                <<BSIM: bsim i1 st_src1 st_tgt1>>)
             \/
             (exists st_src1 tr,
              <<PTERM: ~ trace_intact tr' >> /\
              <<STAR: Star L1 st_src0 tr st_src1>> /\ 
              <<TREL: exists tl, tr_rel (ev_rel gvmap) tr ((trace_cut_pterm tr') ** tl)>>))
      (FINAL: forall retv
                (FINALTGT: final_state L2 st_tgt0 retv),
              exists st_src1,
              <<STEPSRC: Star L1 st_src0 E0 st_src1>> /\
              <<FINALSRC: final_state L1 st_src1 retv>>)
      (PROGRESS: <<FINAL: exists retv, final_state L2 st_tgt0 retv>> \/
                 <<STEP: exists tr st', Step L2 st_tgt0 tr st'>>)
  | bsim_step_stutter
      i1 st_src1
      (ORD: order i1 i0)
      (STAR: Star L1 st_src0 E0 st_src1)
      (BSIM: bsim i1 st_src1 st_tgt0).

  Variant _bsim bsim (i0: index) (st_src0: state L1) (st_tgt0: state L2): Prop :=
  | bsim_intro
      (STEP: forall
            (SAFESRC: safe L1 st_src0),
          <<STEP: bsim_step bsim i0 st_src0 st_tgt0>>).

  Definition bsim: _ -> _ -> _ -> Prop := paco3 _bsim bot3.

  Lemma bsim_mon: monotone3 _bsim.
  Proof.
    ii. inv IN. econs; eauto. i. exploit STEP; eauto. i; des_safe. inv H.
    - econs; eauto. i. exploit STEP0; eauto.
      i. destruct H; des_safe.
      + left; esplits; eauto.
      + right. esplits; eauto.
    - eright; eauto.
  Qed.

End BACKWARD_SIM.

Hint Unfold bsim.
Hint Resolve bsim_mon: paco.

Definition unboundedOrd A (order: A -> A -> Prop) : Prop :=
  forall a, exists a', order a a'.

Lemma unbdd_lex_ord
    A B (ordA: A -> A -> Prop) (ordB: B -> B -> Prop)
    (UNBDDA: unboundedOrd ordA)
    (UNBDDB: unboundedOrd ordB):
  unboundedOrd (lex_ord ordA ordB).
Proof.
  unfold unboundedOrd in *. i. destruct a.
  specialize (UNBDDA a). specialize (UNBDDB b). des.
  exists (a'0, a'). econs; eauto.
Qed.

Record bsim_properties (L1 L2: semantics)
   (index: Type) (order: index -> index -> Prop) : Prop := {
    bsim_order_wf: <<WF: well_founded order>>;
    bsim_initial_states_exist: forall st_init_src
        (INITSRC: initial_state L1 st_init_src),
        exists st_init_tgt, <<INITTGT: initial_state L2 st_init_tgt>>;
    bsim_match_initial_states: forall st_init_src_
        (INITSRC: initial_state L1 st_init_src_)
        st_init_tgt
        (INITTGT: initial_state L2 st_init_tgt)
        st_init_tgt1
        (TGTCAP: initial_capture L2 st_init_tgt st_init_tgt1)
        gmtgt
        (GVMAPTGT: initial_pimap L2 st_init_tgt1 = gmtgt),
      exists i0 st_init_src st_init_src1 gmsrc,
      <<INITSRC: initial_state L1 st_init_src>> /\
      <<SRCCAP: initial_capture L1 st_init_src st_init_src1>> /\
      <<GVMAPSRC: initial_pimap L1 st_init_src1 = gmsrc>> /\
      <<GMSUB: gm_improves gmsrc gmtgt>> /\                                                          
      <<BSIM: @bsim L1 L2 gmtgt index order i0 st_init_src1 st_init_tgt1>>;
}.

Arguments bsim_properties: clear implicits.

Variant backward_simulation (L1 L2: semantics): Prop :=
  Backward_simulation (index: Type)
                      (order: index -> index -> Prop)
                      (props: bsim_properties L1 L2 index order).

Arguments Backward_simulation {L1 L2 index} order props.

(**********************************************************************************************************)
(**********************************************************************************************************)
(**********************************************************************************************************)

(** Aux Lemmas for event relation *)

Lemma evval_rel_mon gm gm'
    (GIMP: gm_improves gm gm'):
  evval_rel gm <2= evval_rel gm'.
Proof.
  ii. unfold evval_rel, eventval_bind in *. des_ifs; des; split; auto.
  - unfold to_int_ev in *. des_ifs.
  - unfold to_int_ev in *. des_ifs_safe. exploit GIMP; eauto. i. erewrite H. eauto.
Qed.

Lemma evval_list_rel_mon gm gm'
    (GIMP: gm_improves gm gm'):
  Forall2 (evval_rel gm) <2= Forall2 (evval_rel gm').
Proof. ii. ginduction PR; ss. i. econs; eauto. eapply evval_rel_mon; eauto. Qed.

Lemma ev_rel_mon gm gm'
    (GIMP: gm_improves gm gm'):
  ev_rel gm <2= ev_rel gm'.
Proof.
  ii. unfold ev_rel, event_rel in *. destruct x0; ss.
  - destruct x1; ss. des; esplits; eauto.
    { eapply evval_list_rel_mon; eauto. }
    { eapply evval_rel_mon; eauto. }
  - destruct x1; ss. des; esplits; eauto. eapply evval_rel_mon; eauto.
  - destruct x1; ss. des; esplits; eauto. eapply evval_rel_mon; eauto.
  - destruct x1; ss. des; esplits; eauto. eapply evval_list_rel_mon; eauto.
Qed.

Lemma tr_rel_mon ev_rel1 ev_rel2
  (EIMP: ev_rel1 <2= ev_rel2):
  @tr_rel ev_rel1 <2= @tr_rel ev_rel2.
Proof. ii. ginduction PR; ii; econs; eauto. eapply IHPR; eauto. Qed.

Lemma tr_improves_trans ev_rel1 ev_rel2 ev_rel3
    (TR1: @tr_improves ev_rel1 ev_rel2)
    (TR2: @tr_improves ev_rel2 ev_rel3) :
  tr_improves ev_rel1 ev_rel3.
Proof. ii. eapply TR2. eapply TR1; eauto. Qed.

(** Lemmas For bsim *)

Lemma bsim_mon_rel
    L1 L2 gm gm' index1 index2 order1 order2 (inj: index1 -> index2)
    (TIMP: gm_improves gm gm')
    (DIMP: forall i1 i2, order1 i1 i2 <0= order2 (inj i1) (inj i2)) i :
  @bsim L1 L2 gm index1 order1 i <2=
  @bsim L1 L2 gm' index2 order2 (inj i).
Proof.
  revert_until DIMP. pcofix CIH. i.
  pstep. econs. i. punfold PR. inv PR.
  exploit STEP; eauto; i. clear STEP. inv H; pclearbot.
  econs; ii.
  - exploit STEP; eauto. i. destruct H; des_safe.
    + left. esplits; pclearbot; eauto.
      { eapply tr_rel_mon. eapply ev_rel_mon; eauto. eauto. }
      des; eauto.
    + right. esplits; pclearbot; eauto.
      { eapply tr_rel_mon. eapply ev_rel_mon; eauto. eauto. }
  - exploit FINAL; eauto.
  - esplits; eauto.
  - econs 2; eauto.
Qed.

Lemma bsim_properties_mon_rel
    L1 L2
    index1 index2 order1 order2 (inj: index1 -> index2)
    (DIMP: forall i1 i2, order1 i1 i2 <0= order2 (inj i1) (inj i2))
    (WF: well_founded order2) :
  bsim_properties L1 L2 index1 order1 ->
  bsim_properties L1 L2 index2 order2.
Proof.
  ii. inv H. econs; eauto. ii.
  exploit bsim_match_initial_states0; eauto. i. des. esplits; eauto.
  eapply bsim_mon_rel; cycle 2; eauto.
  { ii. eauto. }
Qed.

Lemma tc_mon
    idx (order order2: idx -> idx -> Prop) i i'
    (ORD : tc order i i')
    (ORDLE : order <2= order2):
  tc order2 i i'.
Proof.
  ginduction ORD; ii; ss; eauto using t_trans. econs; eauto.
Qed.

Lemma not_intact_pterm tr:
  ~ trace_intact tr <-> In Event_pterm tr.
Proof.
  split; i; eauto. apply NNPP in H; eauto. Qed.

Lemma tr_rel_pterm ev_rel tr tr'
    (EPTM: forall ev1 ev2 (ER: ev_rel ev1 ev2: Prop), ev1 = Event_pterm <-> ev2 = Event_pterm)
    (TREL : tr_rel ev_rel tr tr'):
  ~ trace_intact tr' <-> ~ trace_intact tr.
Proof.
  rewrite !not_intact_pterm.
  move TREL before ev_rel. revert_until TREL.
  induction TREL; i; eauto.
  ss. split; i; des; subst.
  - left. eapply EPTM in H. apply H. eauto.
  - right. eapply IHTREL; eauto.
  - left. eapply EPTM in H. apply H. eauto.
  - right. eapply IHTREL; eauto.
Qed.

Lemma tr_rel_intact ev_rel tr tr'
    (EPTM: forall ev1 ev2 (ER: ev_rel ev1 ev2: Prop), ev1 = Event_pterm <-> ev2 = Event_pterm)
    (TREL : tr_rel ev_rel tr tr'):
  trace_intact tr' <-> trace_intact tr.
Proof.
  unfold trace_intact. rewrite <-!not_intact_pterm, tr_rel_pterm; eauto.
Qed.

Lemma trace_cut_pterm_intact_eq tr
    (INTACT: trace_intact tr):
  trace_cut_pterm tr = tr.
Proof.
  assert (X := trace_cut_pterm_intact_app tr E0 INTACT).
  ss. rewrite !E0_right in *. eauto.
Qed.

Lemma tr_rel_cut_pterm ev_rel tr tr'
    (EPTM: forall ev1 ev2 (ER: ev_rel ev1 ev2: Prop), ev1 = Event_pterm <-> ev2 = Event_pterm)
    (REL: tr_rel ev_rel tr tr'):
  tr_rel ev_rel (trace_cut_pterm tr) (trace_cut_pterm tr').
Proof.
  induction REL; try (by ss; eauto).
  destruct (classic (x = Event_pterm)).
  - rewrite H0. rewrite EPTM in H0; eauto. rewrite H0. ss.
  - rewrite (cons_app x), (cons_app y), !trace_cut_pterm_intact_app; ss.
    + econs; eauto.
    + ii. inv H1; eauto. apply H0. eapply EPTM; eauto.
    + ii. inv H1; eauto.
Qed.

Definition single_events_at (L: semantics) (s:L.(state)) : Prop :=
  forall t s', Step L s t s' -> (length t <= 1)%nat.

Inductive Dfinal_state (L: semantics) (st: L.(state)) (retv: int): Prop :=
| Dfinal_state_intro
    (FINAL: final_state L st retv)
    (DTM: forall retv0 retv1
        (FINAL0: final_state L st retv0)
        (FINAL1: final_state L st retv1),
        retv0 = retv1)
    (DTM: forall retv0
        (FINAL: final_state L st retv0),
        Nostep L st).

Inductive Dinitial_state (L: semantics) (st: L.(state)): Prop :=
| Dinitial_state_intro
    (INIT: initial_state L st)
    (DTM: forall st0 st1
        (INIT0: initial_state L st0)
        (INIT1: initial_state L st1),
        st0 = st1).

Record receptive_at (L: semantics) (s:L.(state)) : Prop :=
  Receptive_at {
    sr_receptive_at: forall t1 s1 t2,
      Step L s t1 s1 -> match_traces L.(symbolenv) t1 t2 -> exists s2, Step L s t2 s2;
    sr_traces_at:
      single_events_at L s
  }.

Record deterministic_at (L: semantics) (s:L.(state)) : Prop :=
  Deterministic_at {
      sd_deterministic_at: forall t1 s1 t2 s2
        (STEP0: Step L s t1 s1)
        (STEP1 :Step L s t2 s2),
        <<EQ: t1 = t2>> /\ <<EQ: s1 = s2>>;
    sd_deterministic_at_final: forall tr s' retv
        (FINAL: final_state L s retv)
        (STEP: Step L s tr s'),
        False;
    sd_deterministic_traces_at:
      single_events_at L s;
    }.

Record determinate_at (L: semantics) (s:L.(state)) : Prop :=
  Determinate_at {
    sd_determ_at: forall t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 ->
      match_traces L.(symbolenv) t1 t2 /\ (t1 = t2 -> s1 = s2);
    sd_determ_at_final: forall
        tr s' retv
        (FINAL: final_state L s retv)
        (STEP: Step L s tr s'),
        False;
    sd_traces_at:
      single_events_at L s
  }.

Definition DStep (L: semantics) :=
  (fun s1 t s2 => deterministic_at L s1 /\ Step L s1 t s2).

Definition DStar (L: semantics) :=
  (star (fun _ => DStep L)) L.(globalenv).

Definition DStarN (L: semantics) :=
  (starN (fun _ => DStep L)) L.(globalenv).

Definition DPlus (L: semantics) :=
  (plus (fun _ => DStep L)) L.(globalenv).

Hint Unfold DStep DStar DStarN DPlus.

Lemma tr_improves_refl (ev_rel: event -> event -> Prop):
  tr_improves ev_rel ev_rel.
Proof. ii. ginduction PR; ii; ss. econs; eauto. Qed.

Definition is_internal (L: semantics): L.(genvtype) -> L.(state) -> Prop := fun ge s => ~ (is_external L ge s).

Definition IStep (L: semantics) :=
  (fun s1 t s2 =>  is_internal L L.(globalenv) s1 /\ Step L s1 t s2).

Definition IStar (L: semantics) :=
  (star (fun _ => IStep L)) L.(globalenv).

Definition IStarN (L: semantics) :=
  (starN (fun _ => IStep L)) L.(globalenv).

Definition IPlus (L: semantics) :=
  (plus (fun _ => IStep L)) L.(globalenv).

Hint Unfold IStep IStar IStarN IPlus.

Section MIXED_SIM.

  Variables L1 L2: semantics.

  Variable gvmap : ident -> option Z.  (* Initial map *)
  
  Variable index: Type.
  Variable order: index -> index -> Prop.

  Inductive fsim_step xsim (i0: index) (st_src0: L1.(state)) (st_tgt0: L2.(state)): Prop :=
  | fsim_step_step
      (STEP: forall st_src1 tr
             (STEPSRC: Step L1 st_src0 tr st_src1),
           exists i1 tr' st_tgt1,
           <<TRREL: tr_rel (ev_rel gvmap) tr tr'>> /\
           ((<<PLUS: DPlus L2 st_tgt0 tr' st_tgt1 /\ (<<RECEPTIVE: receptive_at L1 st_src0>>)>>)
             \/
             <<STUTTER: st_tgt0 = st_tgt1 /\ tr' = E0 /\ order i1 i0>>) /\
            <<XSIM: xsim i1 st_src1 st_tgt1>>)
      (FINAL: forall retv
          (FINALSRC: final_state L1 st_src0 retv),
          <<FINALTGT: Dfinal_state L2 st_tgt0 retv>>)
  | fsim_step_stutter
      i1 st_tgt1
      (PLUS: DPlus L2 st_tgt0 nil st_tgt1 /\ order i1 i0)
      (XSIM: xsim i1 st_src0 st_tgt1).

  Variant _xsim_forward xsim (i0: index) (st_src0: state L1) (st_tgt0: state L2): Prop :=
  | _xsim_forward_intro
      (STEP: fsim_step xsim i0 st_src0 st_tgt0).

  Let bsim_step := bsim_step L1 L2 gvmap order.

  Variant _xsim_backward xsim (i0: index) (st_src0: state L1) (st_tgt0: state L2): Prop :=
  | _xsim_backward_intro
      (STEP: forall
          (SAFESRC: safe L1 st_src0),
          <<STEP: bsim_step xsim i0 st_src0 st_tgt0>>).

  Definition _xsim xsim (i0: index) (st_src0: state L1) (st_tgt0: state L2): Prop :=
    (<<XSIM: (_xsim_forward \4/ _xsim_backward) xsim i0 st_src0 st_tgt0>>).

  Definition xsim: _ -> _ -> _ -> Prop := paco3 _xsim bot3.

  Lemma _xsim_forward_mon: monotone3 (_xsim_forward).
  Proof.
    ii. inv IN. econs; eauto. inv STEP.
    - econs 1; eauto. i. exploit STEP0; eauto. i; des_safe. esplits; eauto.
    - econs 2; eauto.
  Qed.

  Lemma _xsim_backward_mon: monotone3 (_xsim_backward).
  Proof.
    ii. inv IN. econs; eauto. i. exploit STEP; eauto. i; des_safe. inv H.
    - econs; eauto. i. exploit STEP0; eauto. i; des1.
      + left. des_safe. esplits; eauto.
      + des_safe. right. esplits; eauto.
    - eright; eauto.
  Qed.

  Lemma xsim_mon: monotone3 _xsim.
  Proof.
    ii. repeat spc IN. inv IN.
    (* - left. left. eapply _xsim_strict_forward_mon; eauto. *)
    - left. eapply _xsim_forward_mon; eauto.
    - right. eapply _xsim_backward_mon; eauto.
  Qed.

End MIXED_SIM.

Hint Unfold xsim.
Hint Resolve xsim_mon: paco.
Hint Resolve _xsim_forward_mon: paco.
Hint Resolve _xsim_backward_mon: paco.

Inductive xsim_init_sim (L1 L2: semantics)
  (index: Type) (order: index -> index -> Prop) : Prop :=
| xsim_init_forward
    (INITSIM: forall st_init_src
        (INITSRC: initial_state L1 st_init_src),
        exists st_init_tgt,
          (<<INITTGT: Dinitial_state L2 st_init_tgt>>) /\
            (<<CAP: forall st_init_tgt1 (CAPTGT: initial_capture L2 st_init_tgt st_init_tgt1)
                      gmtgt
                      (GVMAPTGT: initial_pimap L2 st_init_tgt1 = gmtgt),
                exists i1 st_init_src1 gmsrc,
                  (<<CAPSRC: initial_capture L1 st_init_src st_init_src1>>) /\
                  (<<GVMAPSRC: initial_pimap L1 st_init_src1 = gmsrc>>) /\
                  (<<GMSUB: gm_improves gmsrc gmtgt>>) /\
                  (<<XSIMCAP: xsim L1 L2 gmtgt order i1 st_init_src1 st_init_tgt1>>)>>))
| xsim_init_backward
    (INITEXISTS: forall st_init_src
        (INITSRC: initial_state L1 st_init_src),
        exists st_init_tgt, <<INITTGT: initial_state L2 st_init_tgt>>)
    (INITSIM: forall st_init_src_
        (INITSRC: initial_state L1 st_init_src_)
        st_init_tgt
        (INITTGT: initial_state L2 st_init_tgt)
        st_init_tgt1
        (TGTCAP: initial_capture L2 st_init_tgt st_init_tgt1)
        gmtgt
        (GVMAPTGT: initial_pimap L2 st_init_tgt1 = gmtgt),
        exists i0 st_init_src st_init_src1 gmsrc,
          (<<INITSRC: initial_state L1 st_init_src>>) /\
          (<<SRCCAP: initial_capture L1 st_init_src st_init_src1>>) /\
          (<<GVMAPSRC: initial_pimap L1 st_init_src1 = gmsrc>>) /\
          (<<GMSUB: gm_improves gmsrc gmtgt>>) /\
          (<<XSIM: xsim L1 L2 gmtgt order i0 st_init_src1 st_init_tgt1>>)).

Record xsim_properties (L1 L2: semantics) (index: Type) (order: index -> index -> Prop) : Prop := {
    xsim_order_wf: <<WF: well_founded order>>;
    xsim_order_unbounded: <<UBD: unboundedOrd order>>;
    xsim_initial_states_sim: <<INIT: xsim_init_sim  L1 L2 order>>;
    xsim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id;
}.

Arguments xsim_properties: clear implicits.

Inductive mixed_simulation (L1 L2: semantics) : Prop :=
  Mixed_simulation (index: Type)
                   (order: index -> index -> Prop)
                   (props: xsim_properties L1 L2 index order).

Arguments Mixed_simulation {L1 L2 index} order props.

Section MIXED_TO_BACKWARD.

Variables L1 L2: semantics.
  
Variable index: Type.
Variable order: index -> index -> Prop.

Hypothesis XSIM: xsim_properties L1 L2 index order.

Variable st_init_tgt st_init_tgt1: L2.(state).
Hypothesis TINIT1: L2.(initial_state) st_init_tgt.
Hypothesis ICAP1: L2.(initial_capture) st_init_tgt st_init_tgt1.

Definition gmtgt : ident -> option Z := L2.(initial_pimap) st_init_tgt1.
Definition ev_rel2 : event -> event -> Prop := ev_rel gmtgt.

Let match_states := xsim L1 L2 gmtgt order.

(** Orders *)

Inductive x2b_index : Type :=
  | X2BI_before (n: nat)
  | X2BI_after (n: nat) (i: index).

Inductive x2b_order: x2b_index -> x2b_index -> Prop :=
  | x2b_order_before: forall n n',
      (n' < n)%nat ->
      x2b_order (X2BI_before n') (X2BI_before n)
  | x2b_order_after: forall n n' i,
      (n' < n)%nat ->
      x2b_order (X2BI_after n' i) (X2BI_after n i)
  | x2b_order_after': forall n m i' i,
      clos_trans _ order i' i ->
      x2b_order (X2BI_after m i') (X2BI_after n i)
  | x2b_order_switch: forall n n' i,
      x2b_order (X2BI_before n') (X2BI_after n i).

Lemma wf_x2b_order:
  well_founded x2b_order.
Proof.
  assert (ACC1: forall n, Acc x2b_order (X2BI_before n)).
  { intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto. }
  assert (ACC2: forall i n, Acc x2b_order (X2BI_after n i)).
  { intros i; pattern i. eapply well_founded_ind.
    { apply wf_clos_trans. eapply xsim_order_wf; eauto. }
    i. pattern n. apply lt_wf_ind; i. clear n. econs; eauto. i. inv H1; eauto. }
  red; intros. destruct a; auto.
Qed.

Lemma unbdd_x2b_order:
  unboundedOrd x2b_order.
Proof.
  r. ii. destruct a.
  - exists (X2BI_before (S n)). econs. lia.
  - exists (X2BI_after (S n) i). econs 2. lia.
Qed.

(** Constructing the backward simulation *)

Inductive x2b_match_states: x2b_index -> state L1 -> state L2 -> Prop :=
  | x2b_match_at: forall i s1 s2,
      match_states i s1 s2 ->
      x2b_match_states (X2BI_after O i) s1 s2
  | x2b_match_before: forall s1 t s1' t' s2b s2 n s2a,
      Step L1 s1 t s1' ->  t <> E0 ->
      DStar L2 s2b E0 s2 ->
      DStarN L2 n s2 t' s2a ->
      tr_rel ev_rel2 t t' ->
      (forall t s1',
         Step L1 s1 t s1' ->
         exists i', exists t', exists s2',
         <<TRREL: tr_rel ev_rel2 t t'>> /\
         ((<<PLUS: DPlus L2 s2b t' s2' /\ (<<RECEPTIVE: receptive_at L1 s1>>)>>)
           \/
           <<STUTTER: s2b = s2' /\ t' = E0>>)
       /\ match_states i' s1' s2') ->
      x2b_match_states (X2BI_before n) s1 s2
  | x2b_match_after: forall n s2 s2a s1 i,
      DStarN L2 (S n) s2 E0 s2a ->
      match_states i s1 s2a ->
      x2b_match_states (X2BI_after (S n) i) s1 s2.

Remark x2b_match_after':
  forall n s2 s2a s1 i,
  DStarN L2 n s2 E0 s2a ->
  match_states i s1 s2a ->
  x2b_match_states (X2BI_after n i) s1 s2.
Proof.
  intros. inv H. econstructor; eauto. econstructor; eauto. econstructor; eauto.
Qed.

Definition x2b_ostar (i0 i1: x2b_index) (st0: L1.(state)) (tr: trace) (st1: L1.(state)) : Prop :=
  <<PLUS: Plus L1 st0 tr st1>> \/ <<STAR: Star L1 st0 tr st1 /\ x2b_order i1 i0>>.

Lemma x2b_ostar_left
    i i' s1 s1' s1'' tr1 tr2
    (STEP : Step L1 s1 tr1 s1')
    (OSTAR : x2b_ostar i i' s1' tr2 s1''):
  exists i1 i1', x2b_ostar i1 i1' s1 (tr1 ** tr2) s1''.
Proof.
  inv OSTAR.
  - esplits; eauto. left. eapply plus_left'; eauto.
  - des. esplits; eauto. left. eapply plus_left; eauto.
Unshelve. all: econs; econs.
Qed.

Lemma x2b_ostar_star_left
    i i' s1 s1' s1'' tr1 tr2
    (STAR : Star L1 s1 tr1 s1')
    (OSTAR : x2b_ostar i i' s1' tr2 s1''):
  exists i1 i1', x2b_ostar i1 i1' s1 (tr1 ** tr2) s1''.
Proof.
  ginduction STAR; i; ss.
  - esplits; eauto.
  - subst. exploit IHSTAR; eauto. i. des. subst.
    exploit x2b_ostar_left; eauto. i. des. traceEq. esplits; eauto.
Qed.

Lemma _xsim_backward_mon_x2b
    i0 st_src0 st_tgt0
    (BSIM: _xsim_backward L1 L2 gmtgt order match_states i0 st_src0 st_tgt0):
  <<BSIM: _xsim_backward L1 L2 gmtgt x2b_order x2b_match_states (X2BI_after 0 i0) st_src0 st_tgt0>>.
Proof.
  red. inv BSIM. econs; eauto. i. exploit STEP; eauto. i; des. inv H.
  - econs 1; eauto. i. exploit STEP0; eauto. i. des1.
    + left. des_safe; pclearbot. inv H0.
      * esplits; eauto; econs; eauto.
      * esplits; eauto.
        { right. des_safe. esplits; eauto. econs 3; eauto. }
        econs; eauto.
    + i. des_safe.
      right. esplits; eauto.
  - pclearbot. des. econs 2; eauto. esplits; eauto. econs 3; eauto. econs; eauto.
Qed.

(** Exploiting mixed simulation *)

Inductive x2b_transitions: index -> state L1 -> state L2 -> Prop :=
  | x2b_trans_forward_final
      i st_src0 st_src1 st_tgt0 r
      (TAU: Star L1 st_src0 E0 st_src1)
      (FINALSRC: final_state L1 st_src1 r)
      (FINALTGT: Dfinal_state L2 st_tgt0 r):
      x2b_transitions i st_src0 st_tgt0
  | x2b_trans_forward_step: forall i s1 s2 s1' t t' s1'' s2' i' i'',
      Star L1 s1 E0 s1' ->
      Step L1 s1' t s1'' ->
      DPlus L2 s2 t' s2' ->
      tr_rel ev_rel2 t t' ->
      forall (STEP: forall st_src1 tr
                 (STEPSRC: Step L1 s1' tr st_src1),
              exists i1 tr' st_tgt1,
              <<TRREL: tr_rel ev_rel2 tr tr'>> /\
              ((<<PLUS: DPlus L2 s2 tr' st_tgt1 /\ (<<RECEPTIVE: receptive_at L1 s1'>>)>>)
                \/
                <<STUTTER: s2 = st_tgt1 /\ tr' = E0 /\ order i1 i'>>) /\
              <<FSIM: match_states i1 st_src1 st_tgt1>>),
        match_states i'' s1'' s2' ->
        x2b_transitions i s1 s2
  | x2b_trans_forward_stutter: forall i s1 s2 s1' s2' i' i'',
      Star L1 s1 E0 s1' ->
      True ->
      DPlus L2 s2 E0 s2' ->
      match_states i'' s1' s2' ->
      forall (ORD0: clos_refl_trans _ order i' i)
        (ORD1: order i'' i'),
        x2b_transitions i s1 s2
  | x2b_trans_backward
      i0 st_src0 st_tgt0
      (BSIM: _xsim_backward L1 L2 gmtgt x2b_order x2b_match_states (X2BI_after 0 i0) st_src0 st_tgt0):
      x2b_transitions i0 st_src0 st_tgt0.

Lemma x2b_transitions_src_tau_rev
      s1 s1' i i' s2
      (STEPSRC: Star L1 s1 E0 s1')
      (ORDER: order i' i)
      (TRANS: x2b_transitions i' s1' s2):
    <<TRANS: x2b_transitions i s1 s2>>.
Proof.
  inv TRANS.
  * eapply x2b_trans_forward_final; try eapply star_trans; eauto.
  * eapply x2b_trans_forward_step; cycle 1; eauto. eapply star_trans; eauto.
  * eapply x2b_trans_forward_stutter; cycle 1; eauto.
    eapply rt_trans; eauto. constructor. auto. eapply star_trans; eauto.
  * eapply x2b_trans_backward; cycle 1; eauto. inv BSIM. econs; eauto. i. hexploit1 STEP.
    { eapply star_safe; eauto. }
    inv STEP.
    - econs 1; eauto.
      + i. exploit STEP0; eauto. i; destruct H; des_safe.
        { left. esplits; eauto. inv H0.
          - left. eapply star_plus_trans; eauto.
          - des_safe. right. esplits; eauto.
            { eapply star_trans; eauto. }
            inv H0.
            + econs. econs; eauto.
            + econs. eapply t_trans; eauto.
            + econs. }
        { right. esplits.
          - eauto.
          - eapply star_trans; eauto.
          - traceEq. eauto. }
      + i. exploit FINAL; eauto. ii. des_safe. esplits; try eapply FINALSRC; eauto. eapply star_trans; eauto.
    - econs 2; try apply BSIM; eauto.
      + inv ORD; try by (econs; eauto). econs. eapply t_trans; eauto.
      + eapply star_trans; eauto.
Qed.

Lemma x2b_progress:
  forall i s1 s2,
    match_states i s1 s2 -> safe L1 s1 -> x2b_transitions i s1 s2.
Proof.
  intros i0; pattern i0. apply well_founded_ind with (R := order). eapply xsim_order_wf; eauto.
  intros i REC s1 s2 MATCH SAFE. dup MATCH. punfold MATCH0. repeat spc MATCH0. des. inv MATCH0; des.
  { (* forward *)
    inversion H; subst. unfold NW in *. destruct (SAFE s1) as [[r FINAL1] | [t [s1' STEP1]]]. apply star_refl.
    - (* final state reached *)
      inv STEP.
      + eapply x2b_trans_forward_final; try eapply star_refl; eauto. eapply FINAL; eauto.
      + des. pclearbot. inv PLUS.
        eapply x2b_trans_forward_stutter; try apply STAR0; try eapply star_refl; eauto.
        { econs; eauto. }
        econs 2; eauto.

    - inv STEP.
      + (* L1 can make one step *)
        hexploit STEP0; eauto. intros [i' [tr' [s2' [TRREL [A MATCH']]]]]. pclearbot.
        assert (B: DPlus L2 s2 tr' s2' \/ (s2 = s2' /\ tr' = E0 /\ order i' i)).
        { des; eauto. }
        clear A. destruct B as [PLUS2 | [EQ1 [EQ2 ORDER]]].
        { eapply x2b_trans_forward_step; try eapply PLUS2; eauto. apply star_refl.
          des_safe.
          i. exploit STEP0; eauto. i; des_safe. pclearbot.
          eexists. exists tr'0. esplits; eauto. }
        subst. inv TRREL. exploit REC; try apply MATCH'; eauto.
        { eapply star_safe; eauto. apply star_one; auto. }
        i. eapply x2b_transitions_src_tau_rev; eauto. apply star_one; ss.
      + des. pclearbot. clears t. clear t. inv PLUS.
        destruct t1, t2; ss. clear_tac.
        eapply x2b_trans_forward_stutter; eauto. apply star_refl. econs; eauto. apply rt_refl.
  }
  { (* backward *)
    econs 4. eapply _xsim_backward_mon_x2b; eauto. eapply _xsim_backward_mon; eauto. i. pclearbot. ss.
  }
Qed.

Lemma xsim_simulation_not_E0:
  forall s1 t s1', Step L1 s1 t s1' -> t <> E0 ->
  forall s2,
    receptive_at L1 s1 ->
    (forall t s1', Step L1 s1 t s1' ->
     exists i', exists t', exists s2',
       tr_rel ev_rel2 t t'
     /\ (DPlus L2 s2 t' s2' \/ (s2 = s2' /\ t' = E0))
     /\ match_states i' s1' s2') ->
    exists i', exists t', exists s2',
      tr_rel ev_rel2 t t'
    /\ DPlus L2 s2 t' s2'
    /\ match_states i' s1' s2'.
Proof.
  intros. exploit H2; eauto. intros [i' [t' [s2' [A [B C]]]]].
  exists i'; exists t'; exists s2'; split; auto. destruct B; auto. des. subst. inv A. clarify.
Qed.

(** Backward simulation of L2 steps *)

Lemma x2b_match_states_bsim
      i0_x2b st_src0 st_tgt0
      (MATCH: x2b_match_states i0_x2b st_src0 st_tgt0):
    <<BSIM: bsim L1 L2 gmtgt x2b_order i0_x2b st_src0 st_tgt0>>.
Proof.
  red. revert_until match_states.
  pcofix CIH. i. rename r into rr. pfold.
  assert(PROGRESS: safe L1 st_src0 ->
                   <<FINAL: exists retv : int, final_state L2 st_tgt0 retv >> \/
                   <<STEP: exists (tr : trace) (st_tgt1 : state L2), Step L2 st_tgt0 tr st_tgt1 >>).
  { (* PROGRESS *)
    generalize dependent st_src0. generalize dependent st_tgt0. pattern i0_x2b.
    eapply (well_founded_ind wf_x2b_order). clear i0_x2b. intros ? IH ? ? ? SAFE. i. inv MATCH.
    + exploit x2b_progress; eauto. intros TRANS; inv TRANS.
      * left. esplits; eauto. apply FINALTGT.
      * rename H2 into PLUS. inv PLUS. unfold DStep in *. des. right; econstructor; econstructor; eauto.
      * right. rename H2 into PLUS. inv PLUS. rename H2 into STEP. inv STEP. esplits; eauto.
      * inv BSIM. specialize (STEP SAFE). inv STEP.
        { eauto. }
        { des. exploit IH; try apply BSIM; eauto. eapply star_safe; eauto. }
    + rename H2 into STARN. inv STARN. inv H3. clarify. unfold DStep in *. des. right; econstructor; econstructor; eauto.
    + rename H into STARN. inv STARN. des. inv H1. right; econstructor; econstructor; eauto.
  }
  econs; eauto.
  assert(FINALLEMMA: forall retv (SAFESRC: safe L1 st_src0) (FINALTGT: final_state L2 st_tgt0 retv),
            exists st_src1, <<STAR: Star L1 st_src0 E0 st_src1 >> /\ <<FINAL: final_state L1 st_src1 retv >>).
  { (* FINAL *)
    clear - MATCH CIH XSIM TINIT1 ICAP1. (* SSSRC SSTGT. *)
    generalize dependent MATCH. generalize dependent st_src0. generalize dependent st_tgt0. pattern i0_x2b.
    eapply (well_founded_ind wf_x2b_order); eauto. i. rename H into IH. clear i0_x2b.
    i. inv MATCH.
    + exploit x2b_progress; eauto. intro TRANS. inv TRANS.
      * assert(retv = r). { inv FINALTGT0. eapply DTM; eauto. } clarify. esplits; eauto.
      * rename H2 into PLUS. inv PLUS. unfold DStep in *. des. exploit sd_deterministic_at_final; eauto. contradiction. 
      * rename H2 into PLUS. inv PLUS. unfold DStep in *. des. exploit sd_deterministic_at_final; eauto. contradiction.
      * inv BSIM. hexploit1 STEP; eauto. inv STEP; eauto.
        des. exploit IH; try apply BSIM; eauto.
        { eapply star_safe; eauto. }
        i; des. esplits; try apply FINAL. eapply star_trans; eauto.
    + rename H2 into STARN. inv STARN. inv H3. clarify. unfold DStep in *. des. exploit sd_deterministic_at_final; eauto. contradiction.
    + rename H into STARN. inv STARN. unfold DStep in *. des. exploit sd_deterministic_at_final; eauto. contradiction.
  }
  { (* STEP *)
    i. inv MATCH.
  - (* 1. At matching states *)
    exploit x2b_progress; eauto. intros TRANS; inv TRANS.
    { (* final *)
      (* 1.1  L1 can reach final state and L2 is at final state: impossible! *)
      econs 1; ss; eauto. i. inv FINALTGT. exploit DTM0; eauto. i; ss.
    }
    { (* forward *)
      (* 1.2  L1 can make 0 or several steps; L2 can make 1 or several matching steps. *)
      econs 1; ss; eauto.
      i. rename H4 into MATCH. inv H2.
      exploit STEP; eauto. intros [i''' [tr'' [s2''' [TRREL''' [STEP''' MATCH''']]]]].
      destruct H4. exploit sd_deterministic_at. eexact H2. eexact H4. eexact STEPTGT. i.
      destruct (silent_or_not_silent t1).
      (* 1.2.1  L2 makes a silent transition *)
      + destruct (silent_or_not_silent t2).
        (* 1.2.1.1  L1 makes a silent transition too: perform transition now and go to "after" state *)
        * des_safe. subst. simpl in *. destruct (star_starN H5) as [n STEPS2].
          left. exists s1''. exists E0. exists (X2BI_after n i''). inv H3. splits; eauto.
          { econs. }
          { econs 1. eapply plus_right; eauto. }
          right. eapply CIH. eapply x2b_match_after'; eauto.
        (* 1.2.1.2 L1 makes a non-silent transition: keep it for later and go to "before" state *)
        * des_safe. subst. simpl in *. destruct (star_starN H5) as [n STEPS2].
          left. exists s1'. exists E0. exists (X2BI_before n). splits.
          { econs. }
          { econs 2. esplits; eauto. econs. }
          right. eapply CIH.
          econs.
          { eauto. }
          { destruct t; ss. inv H3; clarify. }
          { eapply star_one. eauto. }
          { eapply STEPS2. }
          { eauto. }
          intros. exploit STEP; eauto. intros [i'''' [tr''' [s2'''' [A [B MATCH'''']]]]].
          destruct B as [?|[? [? ?]]]; eauto.
          { exists i''''. exists tr'''. exists s2''''. esplits; eauto. }
          { subst. esplits; eauto. }
      (* 1.2.2 L2 makes a non-silent transition, and so does L1 *)
      + des; cycle 1.
        { subst. inv TRREL'''.  inv H3. exploit Eapp_E0_inv; eauto. i. des; clarify. }
        exploit tr_rel_div_r; eauto. i. des; subst.
        exploit not_silent_length. eapply RECEPTIVE; eauto. intros [EQ | EQ].
        { subst. inv H8. clarify. }
        subst t2'. inv H9. rewrite E0_right in *.
        (* make lemma *)
        assert (SAME: tr' = tr'').
        { inv PLUS.
          assert (t1 = tr').
          { inv H6. exploit sd_deterministic_at. eapply H10. eapply STEPTGT. eapply H11. i. des; subst. eauto. }
          subst.
          assert (t2 = E0).
          { destruct t2; ss. destruct tr'; ss. destruct tr'; ss.
            2:{ inv H6. inv H10. exploit sd_deterministic_traces_at0. eauto. i. ss. lia. }
            inv H8. inv H14. inv TRREL'''. inv H15. }
          subst. traceEq. }
        subst.
        (* inv PLUS. *)
        destruct (star_starN H5) as [n STEPS2]. left. exists s1''. exists t1'. exists (X2BI_after n i''). splits.
        { eauto. }
        { econs. eapply plus_right; eauto. }
        right. eapply CIH.
        eapply x2b_match_after'; eauto.
    }
    { econs 1; ss; eauto.
      i. inv H2.
      - destruct t1, t2; ss. clear_tac.
        exploit sd_deterministic_at. apply H4. apply H4. apply STEPTGT. i; des. clarify.
        destruct H4. clear_tac. destruct (star_starN H5) as [n STEPS2]. destruct n.
        + inv STEPS2. ss. left. eexists. exists E0. exists (X2BI_after 0 i''). esplits; eauto.
          * econs.
          * right. esplits; eauto. econs; eauto. eapply clos_t_rt; eauto.
          * right. eapply CIH. econs; eauto.
        + left. eexists. exists E0. exists (X2BI_after (S n) i''). esplits; eauto.
          * econs.
          * right. esplits; eauto. econs; eauto. eapply clos_t_rt; eauto.
          * right. eapply CIH. econs 3; eauto.
    }
    { (* backward *)
      inv BSIM. exploit STEP; eauto. i. inv H0.
      - econs 1; eauto. i. exploit STEP0; eauto. i; des1.
        + des_safe. left. esplits; eauto.
        + des1. des_safe. right. esplits; eauto.
      - econs 2; eauto.
    }
  - (* 2. Before *)
    econs 1; ss; eauto.
    i. inv H2. { inv H3. clarify. } destruct H5.
    exploit sd_deterministic_at. apply H2. apply H5. apply STEPTGT. i; des.
    destruct (silent_or_not_silent t1).
    + (* 2.1 L2 makes a silent transition: remain in "before" state *)
      subst. simpl in *. left. exists st_src0. eexists. exists (X2BI_before n0). splits.
      { econs. }
      { right. split. apply star_refl. constructor. lia. }
      right. eapply CIH; et.
      econstructor; eauto. eapply star_right; eauto.
    + (* 2.2 L2 make a non-silent transition *)
      exploit tr_rel_div_r; eauto. i. des; subst.
      assert(SINGLE : single_events_at L1 st_src0).
      { exploit H4; eauto. i. des; clarify.
        - inv RECEPTIVE; eauto.
        - subst. ii. inv TRREL. exploit Eapp_E0_inv; eauto. i. des; subst; clarify. }
      exploit not_silent_length. eapply SINGLE. eauto. i. des; subst.
      { inv H9. clarify. }
      inv H10. subst. rewrite E0_right in *.
      exploit H4; eauto. i. des.
      2:{ subst. inv TRREL. inv H9. clarify. }
      assert (NOT: t' <> E0).
      { destruct t'; ss. inv TRREL. clarify. }  
      assert (DStar L2 st_tgt0 t' s2').
      { clear - NOT H1 PLUS. eapply plus_star in PLUS. remember E0 as tr' in H1. ginduction H1; ii.
        - eauto.
        - subst. eapply Eapp_E0_inv in Heqtr'. des; subst. eapply IHstar; eauto. inv PLUS.
          { clarify. }
          inv H. inv H0. exploit sd_deterministic_at. eexact H3. eapply H4. eapply H5. i.
          des; subst. traceEq. }
      assert (SAME: t' = tr').
      { inv H10; clarify.
        inv H11. exploit sd_deterministic_at. eexact H10. eapply STEPTGT. eapply H13. i.
        des; subst. destruct t2; traceEq.
        destruct t1, t1'; ss. inv TRREL. destruct t1'; ss.
        2:{ exploit SINGLE; eauto. i. ss. lia. }
        destruct t1; ss; inv H18. }
      subst.
      assert (STARN': exists n', DStarN L2 n' st_tgt1 E0 s2').
      { inv H10; clarify. inv H11.
        exploit sd_deterministic_at. eexact H10. eapply STEPTGT. eapply H13. i. des; subst.
        assert (t2 = E0).
        { clear - EQ. ginduction t1; ss. i. inv EQ; eauto. }
        subst. traceEq. eapply star_starN; eauto. }
      des.
      left. eexists s1'. eexists. eexists. (* exists (X2BI_after n0 i'). splits; cycle 1. *)
      splits; cycle 1.
      { left. eapply plus_one. eauto. }
      { right. eapply CIH; eauto. eapply x2b_match_after'; try eapply H11; eauto. }
      { eauto. }
  - (* 3. After *)
    econs 1; ss; eauto.
    i. inv H. exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
    destruct H2. exploit sd_deterministic_at. eapply H. eexact H1. eexact STEPTGT. i; des. clarify.
    left. exists st_src0. exists E0. exists (X2BI_after n i). splits.
    { econs. }
    { right. split. eapply star_refl. econs. lia. }
    { right. eapply CIH; et.
      eapply x2b_match_after'; eauto. } }
Qed.

End MIXED_TO_BACKWARD.

(** The backward simulation *)

Lemma mixed_to_backward_simulation L1 L2
    (XSIM: mixed_simulation L1 L2):
  backward_simulation L1 L2.
Proof.
  inversion XSIM. eapply Backward_simulation. constructor.
  2:{ inv props. inv xsim_initial_states_sim0; eauto.
      i. exploit INITSIM; eauto. i; des. inv INITTGT. eauto. }
  2:{ i. destruct props.(xsim_initial_states_sim); eauto; cycle 1.
      - subst. exploit INITSIM; eauto. i; des. esplits; eauto.
        eapply bsim_mon_rel.
        { rr. i. eapply H. }
        2:{ eapply x2b_match_states_bsim; eauto. econs; eauto. }
        { ii. instantiate (1:= fun x => x). eauto. }
      - exploit INITSIM; eauto. i; des. inv INITTGT0.
        assert(st_init_tgt = st_init_tgt0).
        { eapply DTM; eauto. }
        clarify. exploit CAP; eauto. i. des. esplits; eauto. eapply bsim_mon_rel.
        { ii. eapply H. }
        2:{ eapply x2b_match_states_bsim; eauto. econs; eauto. }
        { ii. instantiate (1:= fun x => x). ss. } }
  { eapply wf_x2b_order; eauto. }
Qed.

(**********************************************************************************************************)
(**********************************************************************************************************)
(**********************************************************************************************************)

Lemma xsim_mon_rel
    L1 L2 gm gm' index1 index2 order1 order2 (inj: index1 -> index2)
    (TIMP: gm_improves gm gm')
    (DIMP: forall i1 i2, order1 i1 i2 <0= order2 (inj i1) (inj i2)) i:
  @xsim L1 L2 gm index1 order1 i <2=
  @xsim L1 L2 gm' index2 order2 (inj i).
Proof.
  revert_until DIMP. pcofix CIH. i.
  pstep. i. punfold PR. inv PR.
  - econs. inv H. inv STEP.
    + econs. econs.
      * ii. exploit STEP0; eauto. i. des_safe. destruct H0.
        { esplits; pclearbot; eauto. eapply tr_rel_mon. eapply ev_rel_mon; eauto. eauto. }
        { des; subst. esplits; pclearbot; eauto. inv TRREL. econs. }
      * ii. exploit FINAL; eauto.
    + econs. des. econs 2; eauto. right. eapply CIH. pclearbot. eauto.
  - right. inv H. econs. i. exploit STEP; eauto. i. inv H; pclearbot.
    econs; ii.
    + exploit STEP0; eauto. i. destruct H; des_safe.
      * left. esplits; pclearbot; eauto.
        { eapply tr_rel_mon. eapply ev_rel_mon; eauto. eauto. }
        destruct H0; esplits; eauto. right. des_safe; eauto.
      * right. esplits; pclearbot; eauto.
        eapply tr_rel_mon. eapply ev_rel_mon; eauto. eauto.
    + exploit FINAL; eauto.
    + esplits; eauto.
    + econs 2; eauto.
Qed.

Lemma bsim_to_nostutter_bsim
      (L1 L2: semantics) gm
      index i0 st_src0 st_tgt0
      (ord: index -> index -> Prop)
      (WF: well_founded ord)
      (BSIM: bsim L1 L2 gm ord i0 st_src0 st_tgt0):
    <<BSIM: NOSTUTTER.bsim L1 L2 gm (clos_trans _ ord) i0 st_src0 st_tgt0>>.
Proof.
  red. generalize dependent i0. generalize dependent st_src0. generalize dependent st_tgt0.
  pcofix CIH. i. pfold. econs; eauto. i. econs.
  - generalize dependent st_src0. generalize dependent st_tgt0. pattern i0.
    eapply (well_founded_ind WF); eauto. i. rename H into IH.
    punfold BSIM. inv BSIM. exploit STEP; eauto. i; des_safe. inv H.

    + exploit STEP0; eauto. i. des1.
      * left. des_safe. pclearbot. esplits; eauto. inv H0.
        -- left; ss.
        -- des_safe. right; ss. esplits; eauto.
      * right. ss.
    + pclearbot. des. specialize (IH _ ORD).
      exploit IH; eauto.
      { ii. eapply SAFESRC. eapply star_trans; eauto. }
      i; des_safe. des1.
      { left. des_safe.
        esplits; eauto. des.
        * left. eapply star_plus_trans; eauto.
        * right. esplits; eauto. eapply star_trans; eauto.
          apply clos_trans_tn1_iff. econs 2; eauto. apply clos_trans_tn1_iff. ss. }
      { right. des_safe.
        esplits; [eauto| eapply star_trans; eauto| ss; eauto]. }
  - generalize dependent BSIM. generalize dependent st_src0. generalize dependent st_tgt0. pattern i0.
    eapply (well_founded_ind WF); eauto. i. rename H into IH. clear i0.
    punfold BSIM. inv BSIM. hexploit1 STEP; eauto. inv STEP.
    + eapply FINAL; eauto.
    + pclearbot. des.
      hexploit star_safe; eauto. i.
      exploit IH; try eapply H; eauto.
      i; des. esplits; try apply FINALSRC.
      eapply star_trans; eauto.

  - generalize dependent BSIM. generalize dependent st_src0. generalize dependent st_tgt0. pattern i0.
    eapply (well_founded_ind WF); eauto. i. rename H into IH. clear i0.
    punfold BSIM. inv BSIM. specialize (STEP SAFESRC). inv STEP.
    + eauto.
    + des. pclearbot.
      hexploit star_safe; eauto.
Qed.

Lemma backward_to_nostutter_backward_simulation L1 L2
      (BS: backward_simulation L1 L2):
    <<BS: NOSTUTTER.backward_simulation L1 L2>>.
Proof.
  inv BS. inv props. econs; eauto.
  instantiate (1:= (clos_trans _ order)). econs; eauto.
  { eapply well_founded_clos_trans. eauto. }
  i. exploit bsim_match_initial_states0; eauto. i; des.
  esplits; eauto. eapply bsim_to_nostutter_bsim; eauto.
Qed.

