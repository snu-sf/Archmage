
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Registers.
Require Import CSSA.
Require Import SSA.
Require Import SSAutils.
Require Import CSSAgen.
Require Import Utils.
Require Import Kildall.
Require Import KildallComp.
Require Import DLib.
Require Import CSSAgenspec.
Require Import CSSAutils.
Require Import CSSAproof.
Require Import Classical.
Unset Allow StrictProp.

Lemma handle_phi_block_spec_plt_arg_last :
  forall maxreg preds pc block fs_init fs_last
    phicode1 phicode2 parcode1 parcode2,
  handle_phi_block_spec maxreg preds pc
    block fs_init fs_last
    phicode1 phicode2 parcode1 parcode2 ->
  forall arg' args' dst' phib',
  phicode1 ! pc = Some nil ->
  phicode2 ! pc = Some phib' ->
  In (Iphi args' dst') phib' ->
  In arg' args' ->
  Plt arg' fs_last.
Proof.
  intros until parcode2.
  intro H; induction H; intros.
  + assert (RW: phib' = nil) by congruence.
    rewrite RW in *.
    inv H1.
  + inv PBSPECnew_phi.
    rewrite PTree.gss in H1.
    case_eq (list_eq_dec peq args' args'0); intros.
    - rewrite e in *.
      apply Plt_Ple_trans with fs_next; auto.
      eapply gen_new_regs_spec_max_in; eauto.
      eauto.
    - assert (RWphib': phib'
        = Iphi args' fs_init :: phib'0) by congruence.
      rewrite RWphib' in *.
      simpl in H2.
      destruct H2; try congruence.
      eauto.
Qed.

Lemma handle_phi_block_spec_plt_dst_last :
  forall maxreg preds pc block fs_init fs_last
    phicode1 phicode2 parcode1 parcode2,
  handle_phi_block_spec maxreg preds pc
    block fs_init fs_last
    phicode1 phicode2 parcode1 parcode2 ->
  forall args' dst' phib',
  phicode1 ! pc = Some nil ->
  phicode2 ! pc = Some phib' ->
  In (Iphi args' dst') phib' ->
  Plt dst' fs_last.
Proof.
  intros until parcode2.
  intro H; induction H; intros.
  + assert (RW: phib' = nil) by congruence.
    rewrite RW in *.
    inv H1.
  + inv PBSPECnew_phi.
    rewrite PTree.gss in H1.
    case_eq (peq fs_init dst'0); intros.
    - rewrite e in *.
      apply Plt_Ple_trans with (Pos.succ dst'0).
      apply Plt_succ.
      apply Ple_trans with fs_next; eauto.
    - assert (RWphib': phib'
        = Iphi args' fs_init :: phib'0) by congruence.
      rewrite RWphib' in *.
      simpl in H2.
      destruct H2; try congruence.
      eauto.
Qed.

(* NOTE:
  + un prédicat bas niveau (ou def) pour dire l'intervalle de nouvelles
    variables à un point de jonction.
  + un autre pour dire d'un plus haut niveau, que tout est différent
    entre de phi-blocs.
*)

Variant interval_freshness (phicode : phicode) (pc : node) (r1 r2 : positive) : Prop :=
| interval_freshness_intros:
    forall phib,
      phicode ! pc = Some phib ->
      Ple r1 r2 ->
      (forall args dst arg,
          In (Iphi args dst) phib ->
          In arg (dst :: args) ->
          Ple r1 arg /\ Ple arg r2) ->
      interval_freshness phicode pc r1 r2.

Variant disjoint_phis (phicode : phicode)
        (pc pc' : node) : Prop :=
| disjoint_phis_intros:
    forall phib phib',
      phicode ! pc = Some phib ->
      phicode ! pc' = Some phib' ->
      (forall args args' dst dst' arg arg',
          In (Iphi args dst) phib ->
          In arg (dst :: args) ->
          In (Iphi args' dst') phib' ->
          In arg' (dst' :: args') ->
          arg <> arg') ->
      disjoint_phis phicode pc pc'.
  
Lemma disjoint_interval_disjoint :
    forall r1 r2 r3 r4 pc pc' phicode,
    Plt r2 r3 ->
    interval_freshness phicode pc r1 r2 ->
    interval_freshness phicode pc' r3 r4 ->
    disjoint_phis phicode pc pc'.
Proof.
  intros.
  inv H0. inv H1.
  econstructor; eauto; intros.
  assert(Ple arg r2).
  exploit H4; go. tauto.
  assert(Ple r3 arg').
  exploit H6; go. tauto.
  assert(Plt arg arg').
  apply Ple_Plt_trans with (q := r2). auto.
  apply Plt_Ple_trans with (q := r3). auto.
  auto.
  go.
Qed.

Lemma disjoint_interval_comm :
  forall phicode pc pc',
  disjoint_phis phicode pc pc' ->
  disjoint_phis phicode pc' pc.
Proof.
  intros.
  inv H.
  econstructor; go.
  intros.
  assert(arg' <> arg).
  eapply H2; go.
  congruence.
Qed.

Inductive chained_intervals :
    list node -> phicode -> positive -> positive -> Prop :=
| chained_intervals_nil:
    forall phicode init last,
    Ple init last ->
    chained_intervals nil phicode init last
| chained_intervals_cons:
    forall l pc phicode1 phicode2 init last new_init next,
    interval_freshness phicode1 pc new_init next ->
    chained_intervals l phicode2 init last ->
    phicode1 ! pc = phicode2 ! pc ->
    Plt next init ->
    chained_intervals (pc :: l) phicode2 new_init last.

Lemma chained_intervals_ple :
  forall l phicode init last,
  chained_intervals l phicode init last ->
  Ple init last.
Proof.
  intros. induction H. auto.
  apply Ple_trans with (q := init).
  apply Ple_trans with (q := next).
  inv H; auto.
  apply Plt_Ple; auto.
  auto.
Qed.

Lemma chained_intervals_interval :
  forall l phicode init last,
  chained_intervals l phicode init last ->
  forall pc,
  In pc l ->
  exists r1 r2,
    interval_freshness phicode pc r1 r2 /\
    Ple init r1 /\
    Ple r2 last.
Proof.
  intros until last. intro H.
  induction H; intros.
  go.
  inv H3.
  + exists new_init. exists next.
    split; auto.
    inv H; go. econstructor; go. congruence.
    split; auto.
    inv H. apply Ple_refl.
    apply Ple_trans with (q := init).
    apply Plt_Ple; auto.
    eapply chained_intervals_ple; eauto.
  + exploit IHchained_intervals; eauto.
    intros Hinterval.
    destruct Hinterval as [r1 [r2 Hinterval]].
    destruct Hinterval as [Hinterval [Hpleinit Hplelast]].
    exists r1. exists r2.
    split; auto.
    split; auto.
    apply Ple_trans with (q := init).
    apply Ple_trans with (q := next).
    inv H; auto.
    apply Plt_Ple; auto.
    auto.
Qed.

Lemma chained_intervals_left_prolonged :
  forall l phicode init last new_init,
  Ple new_init init ->
  chained_intervals l phicode init last ->
  chained_intervals l phicode new_init last.
Proof.
  intros.
  induction H0.
  constructor.
  apply Ple_trans with (q := init); auto.
  econstructor; eauto.
  inv H0.
  econstructor; eauto.
  apply Ple_trans with (q := new_init0); auto.
  intros.
  exploit H6; eauto; intros HPles.
  destruct HPles.
  split.
  apply Ple_trans with (q := new_init0); auto.
  auto.
Qed.

Inductive chained_disjoint_phis (phicode : phicode) :
    list node -> Prop :=
| chained_disjoint_phis_nil:
    chained_disjoint_phis phicode nil
| chained_disjoint_phis_cons:
    forall l pc,
    chained_disjoint_phis phicode l ->
    (forall pc', In pc' l -> disjoint_phis phicode pc pc') ->
    chained_disjoint_phis phicode (pc :: l).

Lemma chained_intervals_disjoint :
  forall l phicode init last,
  chained_intervals l phicode init last ->
  chained_disjoint_phis phicode l.
Proof.
  intros.
  induction H.
  + go.
  + constructor. auto.
    intros.
    exploit chained_intervals_interval; eauto.
    intros Hinterval.
    destruct Hinterval as [r1 [r2 Hinterval]].
    destruct Hinterval as [Hinterval [Hpleinit Hplelast]].
    assert(interval_freshness phicode2 pc new_init next).
    inv H. econstructor; eauto. congruence.
    clear H.
    apply disjoint_interval_disjoint
      with (r1 := new_init) (r2 := next)
      (r3 := r1) (r4 := r2); auto.
    apply Plt_Ple_trans with (q := init); auto.
Qed.

Lemma chained_disjoint_phis_correct :
  forall l phicode,
  chained_disjoint_phis phicode l ->
  forall pc pc',
  In pc l ->
  In pc' l ->
  pc <> pc' ->
  disjoint_phis phicode pc pc'.
Proof.
  intros until phicode.
  intro H. induction H; intros.
  + inv H.
  + case_eq(peq pc0 pc);
    case_eq(peq pc' pc); go; intros.
    rewrite e in *.
    inv H2; auto. congruence.
    rewrite e in *.
    inv H1; auto. congruence.
    apply disjoint_interval_comm.
    eapply H0; eauto.
    inv H1; go.
    inv H2; go.
Qed.

Definition has_really_phiblock f pc :=
  match (fn_phicode f) ! pc with
  | None => false
  | Some phib => 
      match phib with
      | nil => false
      | _   => true
      end
  end.

Lemma Plt_Ple_succ :
  forall x y,
  Plt x (Pos.succ y) ->
  Ple x y.
Proof.
  intros.
  exploit Plt_succ_inv; eauto. intros.
  destruct H0; go.
  rewrite H0.
  apply Ple_refl.
Qed.

Lemma mfold_copy_node_other_preserves_phicode :
  forall f pc l s u s' INCR,
  wf_ssa_function f ->
  normalized_jp f ->
  ~ In pc l ->
  NoDup l ->
  Plt (get_maxreg f) (next_fresh_reg s) ->
  mfold_unit
    (copy_node (make_predecessors (fn_code f) successors_instr)
      (fn_code f) (fn_phicode f)) l s = OK u s' INCR ->
  (st_phicode s) ! pc = (st_phicode s') ! pc.
Proof.
  induction l; intros until INCR;
  intros WF Hnorm Hnotin HNoDup Hmaxreg.
  + intros. simpl in *.
    unfold ret in H. go.
  + intros.
    simpl in *.
    monadInv H.
    replace ((st_phicode s') ! pc)
      with ((st_phicode s0) ! pc).
    {
      case_eq((fn_phicode f) ! a); intros.
      + case_eq((make_predecessors (fn_code f) successors_instr)
          ! a); intros. 
        eapply copy_node_cssagen_spec_phicode_other; eauto.
        {
          unfold copy_node in EQ.
          flatten EQ.
          unfold node in *.
          congruence.
          unfold error in EQ.
          congruence.
        }
      + unfold copy_node in EQ.
        flatten EQ.
        unfold ret in EQ.
        assert(EQs: s = s0) by congruence.
        rewrite EQs. auto.
    }
    eapply IHl; eauto.
    inv HNoDup; auto.
    apply Plt_Ple_trans with (q :=  (next_fresh_reg s)).
    auto.
    inversion INCR0; auto.
Qed.

Lemma copy_node_nophib_preserves_phicode :
  forall f pc s u s' INCR,
  wf_ssa_function f ->
  normalized_jp f ->
  copy_node (make_predecessors (fn_code f) successors_instr)
    (fn_code f) (fn_phicode f) pc s = OK u s' INCR ->
  (fn_phicode f) ! pc = None ->
  (st_phicode s) ! pc = (st_phicode s') ! pc.
Proof.
  intros.
  unfold copy_node in H1.
  flatten H1.
  unfold ret in H1. go.
Qed.

Lemma mfold_copy_node_nophib_preserves_phicode :
  forall f pc l s u s' INCR,
  wf_ssa_function f ->
  normalized_jp f ->
  NoDup l ->
  Plt (get_maxreg f) (next_fresh_reg s) ->
  mfold_unit
    (copy_node (make_predecessors (fn_code f) successors_instr)
      (fn_code f) (fn_phicode f)) l s = OK u s' INCR ->
  (fn_phicode f) ! pc = None ->
  (st_phicode s) ! pc = (st_phicode s') ! pc.
Proof.
  induction l; intros until INCR; intros WF Hnorm HNoDup Hplt.
  simpl. intros. unfold ret in H. go.
  intros; simpl in *.
  monadInv H.
  case_eq(peq a pc); intros.
  + rewrite e in *.
    replace ((st_phicode s') ! pc)
      with ((st_phicode s0) ! pc).
    eapply copy_node_nophib_preserves_phicode; eauto.
    inv HNoDup.
    eapply IHl; eauto.
    apply Plt_Ple_trans with (q :=  (next_fresh_reg s)).
    auto.
    inversion INCR0; auto.
  + replace ((st_phicode s') ! pc)
      with ((st_phicode s0) ! pc).
    case_eq((fn_phicode f) ! a); intros.
    - case_eq((make_predecessors (fn_code f) successors_instr)
        ! a); intros. 
      eapply copy_node_cssagen_spec_phicode_other; eauto.
      {
        unfold copy_node in EQ.
        flatten EQ.
        unfold node in *.
        congruence.
        unfold error in EQ.
        congruence.
      }
    - unfold copy_node in EQ.
      flatten EQ.
      unfold ret in EQ.
      assert(EQs: s = s0) by congruence.
      rewrite EQs. auto.
    - inv HNoDup.
      eapply IHl; eauto.
      apply Plt_Ple_trans with (q := (next_fresh_reg s)).
      auto.
      inversion INCR0; auto.
Qed.

Lemma handle_phi_real_block_does_incr :
  forall l phi phib pc s x s' INCR,
  handle_phi_block l (phi :: phib) pc s = OK x s' INCR ->
  Plt (next_fresh_reg s) (next_fresh_reg s').
Proof.
  intros.
  simpl in *.
  flatten H.
  monadInv H.
  apply Plt_Ple_trans with
    (q := (next_fresh_reg s0)).
  unfold gen_newreg in EQ.
  flatten EQ. simpl. apply Plt_succ.
  inversion INCR1; auto.
Qed.

Lemma mfold_copy_node_correct_more :
  forall f,
  wf_ssa_function f ->
  normalized_jp f ->
  forall l
    u s s' incr,
  mfold_unit (copy_node
    (make_predecessors (fn_code f) successors_instr)
    (fn_code f) (fn_phicode f))
    l s = OK u s' incr ->
  Plt (get_maxreg f) (next_fresh_reg s) ->
  NoDup l ->
  chained_intervals (filter (has_really_phiblock f) l) (st_phicode s')
    (next_fresh_reg s) (next_fresh_reg s').
Proof.
  intros f WF Hnorm.
  induction l; intros.
  + simpl in *.
    unfold ret in H.
    assert(EQs: s = s') by congruence.
    rewrite EQs.
    constructor.
    apply Ple_refl.
  + simpl in *.
    monadInv H. flatten.
    {
      unfold has_really_phiblock in Eq. flatten Eq.
      unfold copy_node in EQ.
      flatten EQ; [ idtac | unfold error in EQ; congruence].
      monadInv EQ.
      assert(Hnot1: (next_fresh_reg s0) <> 1%positive).
      {
        assert
          (Plt (next_fresh_reg s2) (next_fresh_reg s0)).
        eapply handle_phi_real_block_does_incr; eauto.
        assert(Plt (get_maxreg f) (next_fresh_reg s2)).
        apply Plt_Ple_trans with (q := (next_fresh_reg s)); auto.
        apply Ple_trans with (q := (next_fresh_reg s1)); auto.
        inversion INCR1; auto.
        inversion INCR3; auto.
        unfold not; intros Hun.
        rewrite Hun in H.
        exploit Plt_1; eauto.
      }
      constructor 2
        with (phicode1 := (st_phicode s0))
        (init := (next_fresh_reg s0))
        (next := Pos.pred (next_fresh_reg s0)).
      - (* Maintenant, faut sortir handle_phi_block *)
        exploit handle_phi_block_spec_from_handle_phi_block; eauto.
        intros Hblockspec.
        assert (phib_init: (st_phicode s2) ! a = Some nil).
        replace (st_phicode s2) with (st_phicode s1).
        eapply initialize_phi_block_correct; eauto.
        eapply initialize_parcopy_blocks_correct_other; eauto.
        assert (HEphib': exists phib',
          (st_phicode s0) ! a = Some phib')
         by (eapply handle_phi_block_spec_exists_phib'; eauto).
        destruct HEphib' as [phib' Hphib'].
        apply interval_freshness_intros with (phib := phib'); auto.
        {
          apply Ple_trans with (q := (next_fresh_reg s2)).
          apply Ple_trans with (q := (next_fresh_reg s1)).
          inversion INCR1; go.
          inversion INCR3; go.
          apply Plt_Ple_succ.
          rewrite Pos.succ_pred; auto.
          eapply handle_phi_real_block_does_incr; eauto.
        }
        intros.
        split.
        apply Ple_trans with (q := (next_fresh_reg s2)).
        apply Ple_trans with (q := (next_fresh_reg s1)).
        inversion INCR1; go.
        inversion INCR3; go.
        case_eq(peq arg dst); intros.
        rewrite e.
        eapply handle_phi_block_spec_ple_init_dst; eauto.
        inv H2; go.
        eapply handle_phi_block_spec_ple_init_arg; eauto.
        case_eq(peq arg dst); intros.
        rewrite e.
        apply Plt_Ple_succ.
        rewrite Pos.succ_pred.
        eapply handle_phi_block_spec_plt_dst_last; eauto. congruence.
        apply Plt_Ple_succ.
        rewrite Pos.succ_pred.
        eapply handle_phi_block_spec_plt_arg_last; eauto.
        inv H2; go. congruence.
      - eapply IHl; eauto.
        apply Plt_Ple_trans with (q := (next_fresh_reg s)).
        auto. inversion INCR; auto.
        inv H1; auto.
      - inv H1.
        unfold has_really_phiblock in Eq.
        flatten Eq.
        eapply mfold_copy_node_other_preserves_phicode; eauto.
        apply Plt_Ple_trans with (q := (next_fresh_reg s)).
        auto. inversion INCR; auto.
      - rewrite <- Pos.succ_pred.
        apply Plt_succ. 
        auto.
    }
    unfold has_really_phiblock in Eq.
    flatten Eq.
    - assert(Ple (next_fresh_reg s) (next_fresh_reg s0)).
      inversion INCR; auto.
      assert(
        chained_intervals (filter (has_really_phiblock f) l)
          (st_phicode s') (next_fresh_reg s0)
          (next_fresh_reg s')).
      eapply IHl; auto. eauto.
      apply Plt_Ple_trans with (q := next_fresh_reg s); auto.
      inv H1; auto.
      eapply chained_intervals_left_prolonged; eauto.
    - unfold copy_node in EQ.
      flatten EQ.
      unfold ret in EQ.
      assert(EQs: s = s0) by congruence.
      rewrite EQs in *.
      eapply IHl; eauto.
      inv H1; auto.
Qed.

Lemma check_nodup_in_reglist_correct_aux :
  forall l visited visited' r,
  check_nodup_in_reglist l visited = (true, visited') ->
  SSARegSet.In r visited ->
  ~ In r l.
Proof.
  induction l; intros.
  go.
  simpl in *.
  flatten H.
  unfold not; intros Hinornot.
  destruct Hinornot.
  rewrite H1 in *.
  exploit SSARegSet.mem_1; go. go.
  exploit IHl; go.
  unfold reg_use.
  apply SSARegSet.MF.add_2; auto.
Qed.

Lemma check_nodup_in_reglist_correct :
  forall l visited visited',
  check_nodup_in_reglist l visited = (true, visited') ->
  NoDup l.
Proof.
  induction l; intros.
  constructor.
  simpl in *.
  flatten H.
  constructor.
  eapply check_nodup_in_reglist_correct_aux; eauto.
  unfold reg_use.
  apply SSARegSet.MF.add_1; auto.
  go.
Qed.

Lemma check_nodup_in_reglist_correct_2aux :
  forall l visited visited' r,
  check_nodup_in_reglist l visited = (true, visited') ->
  SSARegSet.In r visited ->
  SSARegSet.In r visited'.
Proof.
  induction l; intros; simpl in *.
  go.
  flatten H.
  eapply IHl; eauto.
  apply SSARegSet.MF.add_2; auto.
Qed.

Lemma check_nodup_in_reglist_correct_2 :
  forall l visited visited' r,
  check_nodup_in_reglist l visited = (true, visited') ->
  In r l ->
  SSARegSet.In r visited'.
Proof.
  induction l; intros.
  inv H0.
  simpl in *.
  flatten H.
  destruct H0.
  + rewrite H0 in *.
    eapply check_nodup_in_reglist_correct_2aux; eauto.
    apply SSARegSet.MF.add_1; auto.
  + go.
Qed.

Lemma check_nodup_in_reglist_correct_3 :
  forall l visited visited' r,
  check_nodup_in_reglist l visited = (true, visited') ->
  SSARegSet.In r visited' ->
  ~ SSARegSet.In r visited ->
  In r l.
Proof.
  induction l; intros; simpl in *.
  go.
  flatten H.
  case_eq (peq a r); intros.
  + left; auto.
  + right.
    eapply IHl; eauto.
    unfold not; intros.
    exploit SSARegSet.add_3; eauto.
Qed.

Fixpoint check_nodup_in_phib phib visited :=
  match phib with
  | nil => true
  | Iphi args dst :: phib' =>
      let '(test, visited') :=
        check_nodup_in_reglist (dst :: args) visited in
      if test
      then check_nodup_in_phib phib' visited'
      else false
  end.

Lemma check_nodup_in_reglist_false :
  forall l visited visited' t,
  (forall r : SSARegSet.elt,
    SSARegSet.In r visited -> SSARegSet.In r visited') ->
  check_nodup_in_reglist l visited = (false, t) ->
  exists t',
  check_nodup_in_reglist l visited' = (false, t').
Proof.
  induction l; go.
  intros. simpl in *.
  flatten H0.
  + exists visited'.
    exploit (H a); eauto.
    apply SSARegSet.mem_2; auto.
    intros.
    assert(SSARegSet.mem a visited' = true).
    apply SSARegSet.mem_1; auto.
    flatten.
  + exploit (IHl (reg_use a visited) (reg_use a visited'));
      eauto; intros.
    {
      case_eq(peq a r); intros.
      - rewrite e in *.
        eapply SSARegSet.add_1; eauto.
      - eapply SSARegSet.add_2; eauto.
        assert(Hin: SSARegSet.In r visited).
        eapply SSARegSet.add_3; eauto.
        unfold not; intros; destruct a; destruct r; intuition go.
        }
    case_eq(SSARegSet.mem a visited'); eauto.
Qed.

Lemma check_nodup_in_phib_preserves_true :
  forall phib visited visited',
  (forall r, SSARegSet.In r visited -> SSARegSet.In r visited') ->
  check_nodup_in_phib phib visited' = true ->
  check_nodup_in_phib phib visited = true.
Proof.
  induction phib; intros; simpl in *; auto.
  flatten; flatten H0.
  + apply IHphib with (visited' := t0); eauto.
    intros.
    case_eq(peq r0 r); intros.
    - rewrite e in *.
      eapply check_nodup_in_reglist_correct_2aux; eauto.
      eapply SSARegSet.add_1; eauto.
    - assert(Hinornot: In r0 l \/ ~ In r0 l) by apply classic.
      destruct Hinornot.
      eapply check_nodup_in_reglist_correct_2; eauto.
      assert(SSARegSet.In r0 visited).
      apply Peirce; intros.
      exploit check_nodup_in_reglist_correct_3; go.
      unfold not; intros.
      apply H4.
      eapply SSARegSet.add_3 in H5; eauto.
      eapply check_nodup_in_reglist_correct_2aux; eauto.
      eapply SSARegSet.add_2; eauto.
  + exfalso.
    exploit (H r); eauto; intros.
    eapply SSARegSet.mem_2; eauto.
    assert(SSARegSet.mem r visited' = true).
    eapply SSARegSet.mem_1; eauto.
    congruence.
  + exfalso.
    exploit (check_nodup_in_reglist_false l (reg_use r visited)
      (reg_use r visited')); eauto; intros. 
    {
      case_eq(peq r0 r); intros.
      - rewrite e in *.
        eapply SSARegSet.add_1; eauto.
      - eapply SSARegSet.add_2; eauto.
        assert(SSARegSet.In r0 visited).
        eapply SSARegSet.add_3; eauto.
        unfold not; intros; destruct r; destruct r0; intuition go.
    }
    destruct H1; congruence.
Qed.
  
Lemma check_nodup_in_phib_correct_for_dst :
  forall phib visited,
  check_nodup_in_phib phib visited = true ->
  forall args dst,
  In (Iphi args dst) phib ->
  ~ SSARegSet.In dst visited.
Proof.
  induction phib; intros.
  inv H0.
  simpl in *.
  flatten H.
  destruct H0.
  + assert(EQ: r = dst) by go.
    rewrite EQ in *.
    unfold not; intros.
    exploit SSARegSet.mem_1; go.
  + apply IHphib with (args := args); auto.
    apply check_nodup_in_phib_preserves_true
      with (visited' := t); eauto.
    intros.
    eapply check_nodup_in_reglist_correct_2aux; eauto.
    case_eq(peq r0 r); intros.
    - rewrite e in *.
      eapply SSARegSet.add_1; eauto.
    - eapply SSARegSet.add_2; eauto.
Qed.

Lemma check_nodup_in_phib_correct_for_arg :
  forall phib visited,
  check_nodup_in_phib phib visited = true ->
  forall args arg dst,
  In (Iphi args dst) phib ->
  In arg args ->
  ~ SSARegSet.In arg visited.
Proof.
  induction phib; intros.
  inv H0.
  simpl in *.
  flatten H.
  destruct H0.
  + assert(EQ: args = l) by go.
    rewrite EQ in *.
    unfold not; intros.
    exploit check_nodup_in_reglist_correct_aux; eauto.
    eapply SSARegSet.add_2; eauto.
  + apply IHphib with (dst := dst) (args := args); auto.
    apply check_nodup_in_phib_preserves_true
      with (visited' := t); eauto.
    intros.
    eapply check_nodup_in_reglist_correct_2aux; eauto.
    case_eq(peq r0 r); intros.
    - rewrite e in *.
      eapply SSARegSet.add_1; eauto.
    - eapply SSARegSet.add_2; eauto.
Qed.

Inductive nodups_in_phib_spec : phiblock -> Prop :=
| nodups_in_phib_spec_nil :
    nodups_in_phib_spec nil
| nodups_in_phib_spec_cons :
    forall args dst phib,
    (forall args' dst' x y,
      In (Iphi args' dst') phib ->
      In x (dst :: args) ->
      In y (dst' :: args') ->
      x <> y ) ->
    NoDup (dst :: args) ->
    nodups_in_phib_spec phib ->
    nodups_in_phib_spec (Iphi args dst :: phib).

Lemma check_nodup_in_phib_correct :
  forall phib visited,
  check_nodup_in_phib phib visited = true ->
  nodups_in_phib_spec phib.
Proof.
  induction phib; intros.
  + simpl in *. go.
  + simpl in *.
    flatten a.
    constructor; simpl in *; intros.
    { destruct H1; destruct H2.
      - rewrite H1 in *.
        rewrite H2 in *.
        assert(Hinx: SSARegSet.In x t).
        eapply check_nodup_in_reglist_correct_2aux; eauto.
        eapply SSARegSet.add_1; eauto.
        assert(Hnotiny: ~ SSARegSet.In y t).
        eapply check_nodup_in_phib_correct_for_dst; eauto.
        go.
      - rewrite H1 in *.
        assert(Hinx: SSARegSet.In x t).
        eapply check_nodup_in_reglist_correct_2aux; eauto.
        eapply SSARegSet.add_1; eauto.
        assert(Hnotiny: ~ SSARegSet.In y t).
        eapply check_nodup_in_phib_correct_for_arg; eauto.
        go.
      - rewrite H2 in *.
        assert(Hinx: SSARegSet.In x t).
        eapply check_nodup_in_reglist_correct_2; eauto.
        assert(Hnotiny: ~ SSARegSet.In y t).
        eapply check_nodup_in_phib_correct_for_dst; eauto.
        go.
      - assert(Hinx: SSARegSet.In x t).
        eapply check_nodup_in_reglist_correct_2; eauto.
        assert(Hnotiny: ~ SSARegSet.In y t).
        eapply check_nodup_in_phib_correct_for_arg; eauto.
        go.
    }
    constructor.
    eapply check_nodup_in_reglist_correct_aux; eauto.
    eapply SSARegSet.add_1; eauto.
    eapply check_nodup_in_reglist_correct; eauto.
    go.
Qed.

Lemma not_in_dst_and_args :
  forall phib,
  nodups_in_phib_spec phib ->
  forall args dst args' dst',
  In (Iphi args dst) phib ->
  In (Iphi args' dst') phib ->
  ~ In dst args'.
Proof.
  intros phib H.
  induction H; intros.
  inv H.
  inv H2; inv H3.
  + unfold not; intros.
    inv H0. go.
  + inv H0.
    assert(EQ: dst0 = dst) by go.
    rewrite EQ in *.
    unfold not; intros.
    exploit (H args' dst' dst dst); eauto.
  + unfold not; intros.
    assert(EQ: args' = args) by go.
    rewrite EQ in *.
    exploit (H args0 dst0 dst0 dst0); eauto.
  + go.
Qed.

Lemma no_dups_in_phib_dst :
  forall phib,
  nodups_in_phib_spec phib ->
  NoDup (map phib_dst phib).
Proof.
  intros phib H.
  induction H; intros.
  go.
  simpl in *.
  constructor.
  unfold not; intros.
  exploit in_phib_dst_exists_args; eauto.
  intros Hin. destruct Hin as [args0 Hin].
  exploit (H args0 dst dst dst); go.
  auto.
Qed.

Lemma check_phicode_for_dups_in_phib_correct :
  forall f pc phib,
  check_phicode_for_dups_in_phib f = true ->
  (CSSA.fn_phicode f) ! pc = Some phib ->
  nodups_in_phib_spec phib.
Proof.
  intros.
  unfold check_phicode_for_dups_in_phib in H.
  rewrite forallb_forall in H.
  specialize (H (pc, phib)).
  exploit H.
  apply PTree.elements_correct; auto.
  intros.
  eapply check_nodup_in_phib_correct; eauto.
Qed.

Lemma nodups_in_phib_nodups_in_phi :
  forall phib,
  nodups_in_phib_spec phib ->
  forall args dst,
  In (Iphi args dst) phib ->
  NoDup (dst :: args).
Proof.
  intros phib H.
  induction H; go.
  intros.
  inv H2; go.
Qed.

Lemma exists_phib_iff :
  forall f tf pc,
  transl_function f = Errors.OK tf ->
  normalized_jp f ->
  wf_ssa_function f ->
  ((fn_phicode f) ! pc <> None
    <->
   (CSSA.fn_phicode tf) ! pc <> None).
Proof.
  intros. 
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  inv SPEC.
  split; intros.
  + case_eq ((fn_phicode f) ! pc); try congruence; intros.
    exploit SSAutils.fn_phicode_code; go.
    intros Hsomeins.
    destruct Hsomeins as [ins Hsomins].
    specialize (H4 pc ins 0).
    exploit H4; eauto; intros Hspec.
    inv Hspec; go.
    rewrite <- fn_phicode_inv in H3; auto.
    inv H3.
    assert(Hpreds_bis:
      (make_predecessors (fn_code f) successors_instr) ! pc
        = Some lpreds) by auto.
    assert (Hpredseq: lpreds = l) by go.
    rewrite Hpredseq in H11.
    simpl in H11. flatten H11; go.
  + unfold transl_function in H.
    flatten H; simpl in *.
    unfold not; intros.
    contradict H3.
    unfold init_state in Eq. flatten Eq.
    exploit mfold_copy_node_nophib_preserves_phicode; eauto.
    {
      assert(list_norepet (map fst (PTree.elements (fn_code f)))).
      apply PTree.elements_keys_norepet.
      apply list_norepet_NoDup; auto.
    }
    intros; simpl in *.
    apply Plt_succ.
    intros; simpl in *.
    rewrite PTree.gempty in H3. auto. 
Qed.

Lemma exists_phib_iff_none :
  forall f tf pc,
  transl_function f = Errors.OK tf ->
  normalized_jp f ->
  wf_ssa_function f ->
  ((fn_phicode f) ! pc = None
    <->
   (CSSA.fn_phicode tf) ! pc = None).
Proof.
  intros.
  split; intros;
  exploit (exists_phib_iff f tf pc); eauto;
  intros; tauto.
Qed.

Definition get_tf s f :=
  {| CSSA.fn_sig := fn_sig f;
     CSSA.fn_params := fn_params f;
     CSSA.fn_stacksize := fn_stacksize f;
     CSSA.fn_code := fn_code f;
     CSSA.fn_phicode := st_phicode s;
     fn_parcopycode := st_parcopycode s;
     CSSA.fn_entrypoint := fn_entrypoint f |}.

Lemma cfgeq_to_star :
  forall f tf pc pc',
  (forall x y, cfg f x y -> CSSA.cfg tf x y) ->
  (cfg f **) pc pc' ->
  (CSSA.cfg tf **) pc pc'.
Proof.
  intros.
  induction H0.
  constructor. auto.
  constructor 2.
  constructor 3 with (y := y); auto.
Qed.

Lemma cfgeq_reached :
  forall f tf pc pc',
  (forall x y, cfg f x y -> CSSA.cfg tf x y) ->
  Dom.reached (cfg f) pc pc' ->
  Dom.reached (CSSA.cfg tf) pc pc'.
Proof.
  intros.
  inv H0.
  constructor. auto.
  constructor 2.
  constructor 3 with (y := y).
  eapply cfgeq_to_star; eauto.
  eapply cfgeq_to_star; eauto.
Qed.

Lemma check_nb_args_correct :
  forall f,
  check_nb_args f
    (CSSA.get_preds f)
    = true ->
  CSSA.block_nb_args f.
Proof.
  intros.
  unfold check_nb_args in H.
  unfold CSSA.block_nb_args.
  intros.
  rewrite forallb_forall in H.
  specialize (H (pc, block)).
  rewrite forallb_forall in H.
  exploit H; eauto; intros.
  apply PTree.elements_correct; auto.
  flatten H2.
  apply beq_nat_true. auto.
Qed.

Lemma check_parcbSome_correct :
  forall f phib pc pred,
  check_parcbSome f
    (CSSA.get_preds f)
    = true ->
  (CSSA.fn_phicode f) ! pc = Some phib ->
  In pred (CSSA.get_preds f) !!! pc ->
  (CSSA.fn_parcopycode f) ! pred <> None.
Proof.
  intros.
  unfold check_parcbSome in H.
  rewrite forallb_forall in H.
  specialize (H (pc, phib)).
  exploit H; eauto; intros.
  apply PTree.elements_correct; auto.
  rewrite forallb_forall in H2.
  specialize (H2 pred).
  exploit H2; eauto; intros.
  flatten H3.
Qed.

Lemma check_parcb'Some_correct :
  forall f phib pc,
  check_parcb'Some f = true ->
  (CSSA.fn_phicode f) ! pc = Some phib ->
  (CSSA.fn_parcopycode f) ! pc <> None.
Proof.
  intros.
  unfold check_parcb'Some in H.
  rewrite forallb_forall in H.
  specialize (H (pc, phib)).
  exploit H; eauto; intros.
  apply PTree.elements_correct; auto.
  flatten H1.
Qed.

Lemma check_fn_parcb_inop_correct :
  forall f pc parcb,
  check_fn_parcb_inop f = true ->
  (CSSA.fn_parcopycode f) ! pc = Some parcb ->
  exists s, (CSSA.fn_code f) ! pc = Some (Inop s).
Proof.
  intros.
  unfold check_fn_parcb_inop in H.
  rewrite forallb_forall in H.
  specialize (H (pc, parcb)).
  exploit H; eauto; intros.
  apply PTree.elements_correct; auto.
  flatten H1. eauto.
Qed.

Lemma wf_fn_phicode_inv :
  forall f tf jp,
  transl_function f = Errors.OK tf ->
  normalized_jp f ->
  wf_ssa_function f ->
  (CSSA.join_point jp tf <-> (CSSA.fn_phicode tf) ! jp <> None).
Proof.
  intros. split; intros.
  - assert(join_point jp f).
    eapply no_new_joinpoints; eauto.
    rewrite fn_phicode_inv in H3; auto.
    assert((CSSA.fn_phicode tf) ! jp <> None).
    eapply exists_phib_iff; eauto.
    go.
  - rewrite <- exists_phib_iff in H2; eauto.
    assert(Hjp: join_point jp f).
    apply fn_phicode_inv; auto.
    inv Hjp.
    econstructor; eauto.
    unfold transl_function in H.
    flatten H. go.
Qed.

Lemma check_fn_parcbjp_correct :
  forall f tf pc parcb pc',
  wf_ssa_function f ->
  normalized_jp f ->
  transl_function f = Errors.OK tf ->
  check_fn_parcbjp tf = true ->
  (CSSA.fn_parcopycode tf) ! pc = Some parcb ->
  (CSSA.fn_code tf) ! pc = Some (Inop pc') ->
  ~ CSSA.join_point pc' tf ->
  CSSA.join_point pc tf.
Proof.
  intros until pc'.
  intros WF Hnorm Htransl Hcheck Hparcb Hinop.
  rewrite wf_fn_phicode_inv; go.
  rewrite wf_fn_phicode_inv; go. intros.
  unfold check_fn_parcbjp in Hcheck.
  rewrite forallb_forall in Hcheck.
  specialize (Hcheck (pc, parcb)).
  exploit Hcheck; eauto.
  apply PTree.elements_correct; auto.
  intros Check.
  flatten Check; go.
  intuition congruence.
Qed.

Lemma cssa_fn_inop_in_jp:
  forall f tf,
  transl_function f = Errors.OK tf ->

  normalized_jp f ->
  wf_ssa_function f ->
  forall pc,
  (CSSA.fn_phicode tf) ! pc <> None ->
  exists succ, (CSSA.fn_code tf) ! pc = Some (Inop succ).
Proof.
  intros f tf Htrans
    Hnorm WF.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans.
  intros.
  inv SPEC; simpl in *.
  assert((fn_phicode f) ! pc <> None).
  rewrite exists_phib_iff; eauto.
  simpl. auto.
  rewrite andb_true_iff in Eq1.
  rewrite andb_true_iff in Eq1.
  destruct Eq1 as [[Check_jp Check_jpinop] Check_entry].
  apply inops_checker_correct; auto.
Qed.

Lemma equiv_phib_phibarg_parcdst :
  forall phib maxreg parcb parcb' phib' k,
  equiv_phib_spec maxreg k phib parcb phib' parcb' ->
  forall args dst arg,
  In (Iphi args dst) phib' ->
  nth_error args k = Some arg ->
  exists src, In (Iparcopy src arg) parcb.
Proof.
  intros until k.
  intros H. induction H; intros.
  go.
  inv H9.
  + assert(EQ1: args0 = args') by congruence.
    assert(EQ2: dst0 = dst') by congruence.
    rewrite EQ1 in *.
    rewrite EQ2 in *.
    assert(EQ3: arg0 = arg') by go.
    rewrite EQ3 in *.
    exists arg; auto.
  + exploit IHequiv_phib_spec; eauto.
    intros Hexists.
    destruct Hexists as [src Hin].
    exists src; go.
Qed.

Lemma equiv_phib_parcb'src_phibdst' :
  forall phib maxreg parcb parcb' phib' k,
  equiv_phib_spec maxreg k phib parcb phib' parcb' ->
  forall src dst,
  In (Iparcopy src dst) parcb' ->
  exists args, In (Iphi args src) phib'.
Proof.
  intros until k.
  intros H. induction H; intros.
  go.
  inv H9.
  + go.
  + exploit IHequiv_phib_spec; eauto.
    intros Hexists.
    destruct Hexists as [args0 Hin].
    exists args0; go.
Qed.

Lemma equiv_phib_phibdst_parcb'src :
  forall phib maxreg parcb parcb' phib' k,
  equiv_phib_spec maxreg k phib parcb phib' parcb' ->
  forall args dst,
  In (Iphi args dst) phib ->
  exists src, In (Iparcopy src dst) parcb'.
Proof.
  intros until k.
  intros H. induction H; intros.
  go.
  inv H9.
  + go.
  + exploit IHequiv_phib_spec; eauto.
    intros Hexists.
    destruct Hexists as [src Hin].
    exists src; go.
Qed.

Lemma phib_nil_phib'_nil:
  forall f tf pc,
  normalized_jp f ->
  wf_ssa_function f ->
  transl_function f = Errors.OK tf ->
  (fn_phicode f) ! pc = Some nil ->
  (CSSA.fn_phicode tf) ! pc <> Some nil ->
  False.
Proof.
  intros f tf pc Hnorm WF Htrans Hnil Hnil'.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  unfold init_state in *.
  unfold transl_function in Htrans.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  flatten Htrans.
  case_eq((CSSA.fn_phicode (get_tf s' f)) ! pc).
  {
    intros phib' Hphib'.
    assert(Hinop: exists succ, (CSSA.fn_code (get_tf s' f)) ! pc
      = Some (Inop succ)).
    eapply cssa_fn_inop_in_jp; eauto. go.
    destruct Hinop as [succ Hinop].

    inv SPEC; simpl in *.
    specialize (H1 pc (Inop succ) 0).
    exploit H1; go; intros.
    inv H0; go.
    + simpl in *. flatten H7.
      assert(Hjp: join_point pc f) by (rewrite fn_phicode_inv in *; go).
      inv Hjp.
      assert((make_predecessors (fn_code f) successors_instr) ! pc = Some nil) by go.
      assert(Hnill: nil = l0) by go. subst. go.
    + inv H11; go.
  }
  intros.
  rewrite <- exists_phib_iff_none in H; go.
  congruence.
Qed.

Lemma In_has_really_phiblock_filter:
  forall f tf pc phib r args,
  normalized_jp f ->
  wf_ssa_function f ->
  transl_function f = Errors.OK tf ->
  (CSSA.fn_phicode tf) ! pc = Some phib ->
  In (Iphi args r) phib ->
  In pc (filter (has_really_phiblock f)
    (map fst (PTree.elements (fn_code f)))).
Proof.
  intros f tf pc phib r args Hnorm WF Htrans Hphib HIn.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  unfold init_state in *.
  unfold transl_function in Htrans.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  flatten Htrans.

  apply filter_In.
  assert(Hinop: exists succ, (CSSA.fn_code (get_tf s' f)) ! pc
    = Some (Inop succ)).
  eapply cssa_fn_inop_in_jp; eauto. go.
  simpl in Hinop.
  destruct Hinop as [succ Hinop].
  assert(In (pc, Inop succ) (PTree.elements (fn_code f))).
  apply PTree.elements_correct; auto.
  split; auto.
  flatten EQ.
  eapply In_Infst; eauto.
  unfold has_really_phiblock.
  flatten; simpl in *.
  + exfalso. eapply phib_nil_phib'_nil; go. simpl.
    unfold not; intros.
    assert(Heqphibs: phib = nil) by go.
    rewrite Heqphibs in *. go.
  + rewrite exists_phib_iff_none in Eq3; go.
    simpl in *. go.
Qed.

Lemma use_code_plemaxreg:
  forall f r pc,
  use_code f r pc ->
  wf_ssa_function f ->
  Ple r (get_maxreg f).
Proof.
  intros.
  inv H;
  match goal with
  | H: (fn_code f) ! pc = Some ?ins |- _ =>
    try solve [apply Ple_trans with
    (get_max_reg_in_ins ins);
    [ unfold get_max_reg_in_ins;
      apply max_reg_in_list_correct; go | 
      apply Ple_trans with
        (get_max_reg_in_code (fn_code f));
      [eapply max_reg_in_code; eauto | apply max_reg_correct_code]]]
  | _ => idtac
  end.
  apply Ple_trans with
  (get_max_reg_in_ins
    (Icall sig (inl r0) args dst s)).
  unfold get_max_reg_in_ins.
  apply max_reg_in_list_correct.
  inv H2; go.
  apply Ple_trans with
    (get_max_reg_in_code (fn_code f)).
  eapply max_reg_in_code; eauto.
  apply max_reg_correct_code.
Qed.

Lemma assigned_code_plemaxreg:
  forall f r pc,
  assigned_code_spec (fn_code f) pc r ->
  wf_ssa_function f ->
  Ple r (get_maxreg f).
Proof.
  intros.
  inv H;
  match goal with
  | H: (fn_code f) ! pc = Some ?ins |- _ =>
    try solve [apply Ple_trans with
    (get_max_reg_in_ins ins);
    [ unfold get_max_reg_in_ins;
      apply max_reg_in_list_correct; go | 
      apply Ple_trans with
        (get_max_reg_in_code (fn_code f));
      [eapply max_reg_in_code; eauto | apply max_reg_correct_code]]]
  | _ => idtac
  end.
  apply Ple_trans with
  (get_max_reg_in_ins
    (Icall sig fn args r succ)).
  unfold get_max_reg_in_ins.
  flatten.
  apply max_reg_in_list_correct. go.
  apply max_reg_in_list_correct. go.
  apply Ple_trans with
    (get_max_reg_in_code (fn_code f)).
  eapply max_reg_in_code; eauto.
  apply max_reg_correct_code.
Qed.

Lemma assigned_phi_pltmaxreg_r:
  forall f tf r pc,
  transl_function f = Errors.OK tf ->

  (* validations *)
  normalized_jp f ->
  assigned_phi_spec (CSSA.fn_phicode tf) pc r ->
  wf_ssa_function f ->
  Plt (get_maxreg f) r.
Proof.
  intros f tf r pc Htrans Hnorm Hphi WF.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans.
  unfold init_state in *.
  inv Hphi.
  inv SPEC; simpl in *.
  assert(Hinop: exists succ, (CSSA.fn_code (get_tf s' f)) ! pc
    = Some (Inop succ)).
  eapply cssa_fn_inop_in_jp; eauto. go.
  simpl in Hinop.
  destruct Hinop as [succ0 Hinop].
  specialize (H3 pc (Inop succ0) 0).
  exploit H3; eauto; intros.
  inv H2; go.
  rewrite exists_phib_iff_none in H7; go.
  go. simpl in *. flatten H9; go; simpl in *.
  {
    assert(Hjp: join_point pc f). rewrite fn_phicode_inv in *; go.
    inv Hjp.
    unfold node in *.
    assert(Hnill: nil = l) by go.
    rewrite <- Hnill in Hl. simpl in Hl. go.
  }
  destruct H0.
  assert(EQphibs: phiinstr = phib') by go.
  rewrite EQphibs in *.
  assert(Plt (get_maxreg f) r).
  eapply equiv_phib_spec_plt_maxreg_phib'dst; eauto.
  auto.
Qed.

Lemma assigned_parc_pltmaxreg_notjp:
  forall f tf r pc,
  transl_function f = Errors.OK tf ->
  wf_ssa_function f ->
  normalized_jp f ->
  check_fn_parcb_inop tf = true ->
  check_fn_parcbjp tf = true ->
  assigned_parcopy_spec (CSSA.fn_parcopycode tf) pc r ->
  ~ join_point pc f ->
  Plt (get_maxreg f) r.
Proof.
  intros f tf r pc Htrans WF Hnorm Checkinop Checkjp Hassign Hnotjp.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans.
  unfold init_state in *.
  simpl in *.
  inv Hassign.
  exploit check_fn_parcb_inop_correct; eauto.
  intros Hinop.
  destruct Hinop as [succ Hinop].
  simpl in *.
  destruct H0 as [src Hin].
  assert(Hjp: CSSA.join_point succ (get_tf s' f)).
  apply Peirce. intros.
  assert(CSSA.join_point pc (get_tf s' f)).
  eapply check_fn_parcbjp_correct; go.
  exploit no_new_joinpoints; eauto; intros.
  go.
  assert(Hinopsucc: exists s, (fn_code f) ! succ = Some (Inop s)).
  exploit no_new_joinpoints; eauto; intros.
  rewrite andb_true_iff in Eq1.
  rewrite andb_true_iff in Eq1.
  destruct Eq1 as [[Check_jp Check_jpinop] Check_entry].
  exploit inops_checker_correct; eauto.
  apply fn_phicode_inv; auto.
  destruct Hinopsucc as [succ' Hinopsucc].
  inv SPEC; simpl in *.
  exploit (is_edge_pred f pc succ); eauto.
  go.
  intros Hindex.
  destruct Hindex as [k Hindex].
  exploit (H2 succ (Inop succ') k); eauto; intros Hcssa.
  inv Hcssa.
  rewrite exists_phib_iff_none in H1; go.
  exploit no_new_joinpoints; eauto; intros Hjpsucc.
  rewrite fn_phicode_inv in Hjpsucc.
  rewrite exists_phib_iff in Hjpsucc; eauto.
  congruence.
  auto.
  {
    exploit index_pred_some_nth; eauto; intros. 
    unfold successors_list in H8.
    unfold node in *.
    rewrite H6 in H8.
    congruence.
  }
  exploit equiv_phib_spec_correct; eauto; intros.
  assert(EQpcpred: pred = pc).
  eapply index_preds_pc_inj; eauto.
  rewrite EQpcpred in *.
  assert(EQparcbs: parcb0 = parcb) by go.
  rewrite EQparcbs in *.
  eapply equiv_phib_fresh_parcb; eauto.
Qed.

Lemma parcb'dst_is_phibdst :
  forall maxreg k phib parcb phib' parcb',
  equiv_phib_spec maxreg k phib parcb phib' parcb' ->
  forall src dst,
  In (Iparcopy src dst) parcb' ->
  exists args,
    In (Iphi args dst) phib.
Proof.
  intros until parcb'.
  intro H.
  induction H; go.
  intros src dst0 Hin.
  inv Hin.
  assert(EQ: dst0 = dst) by go.
  rewrite EQ in *.
  exists args. go.
  exploit IHequiv_phib_spec; eauto.
  intros Hin.
  destruct Hin as [args0 Hin].
  exists args0. go.
Qed.

Lemma parcbsrc_is_phibarg :
  forall maxreg k phib parcb phib' parcb',
  equiv_phib_spec maxreg k phib parcb phib' parcb' ->
  forall src dst,
  In (Iparcopy src dst) parcb ->
  exists args dst',
    In (Iphi args dst') phib /\
    nth_error args k = Some src.
Proof.
  intros until parcb'.
  intro H.
  induction H.
  intros. inv H.
  intros src dst0 Hin.
  inv Hin.
  go.
  exploit (IHequiv_phib_spec src dst0); eauto.
  intros Hexists.
  destruct Hexists as [args0 Hexists].
  destruct Hexists as [dst'0 Hexists].
  exists args0. exists dst'0.
  destruct Hexists.
  split; go.
Qed.

Lemma assigned_parcjp_assigned_phi:
  forall f tf r pc,
  transl_function f = Errors.OK tf ->

  normalized_jp f ->
  wf_ssa_function f ->
  assigned_parcopy_spec (CSSA.fn_parcopycode tf) pc r ->
  join_point pc f ->
  assigned_phi_spec (fn_phicode f) pc r.
Proof.
  intros f tf r pc Htrans Hnorm WF Hassign Hjp.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans. flatten Htrans.
  inv Hassign.
  destruct H0 as [src Hin].
  rewrite fn_phicode_inv in Hjp; auto.
  assert(Hinop: exists succ, (CSSA.fn_code (get_tf s' f)) ! pc =
    Some (Inop succ)).
  eapply cssa_fn_inop_in_jp; eauto.
  rewrite <- exists_phib_iff; eauto.
  destruct Hinop as [succ Hinop].
  inv SPEC.
  exploit (H2 pc (Inop succ) 0); eauto; intros.
  simpl in *.
  inv H1; go.
  {
      simpl in H8. flatten H8; simpl in *.
      assert(Hjp2: join_point pc f). rewrite fn_phicode_inv in *; go.
      inv Hjp2.
      unfold node in *.
      assert(Hnill: nil = l0) by go.
      rewrite <- Hnill in Hl. simpl in Hl. go.
  }
  assert(EQ1: parcb' = parcb) by go.
  rewrite EQ1 in *.
  exploit parcb'dst_is_phibdst; go.
Qed.

Lemma check_parcborparcb'_correct:
  forall f tf pc,
  wf_ssa_function f ->
  normalized_jp f ->
  transl_function f = Errors.OK tf ->
  check_parcborparcb' tf = true ->
  (CSSA.fn_parcopycode tf) ! pc <> None ->
  exists pc',
  (fn_code f) ! pc = Some (Inop pc') /\
  ((CSSA.fn_phicode tf) ! pc <> None \/
   (CSSA.fn_phicode tf) ! pc' <> None).
Proof.
  intros until pc.
  intros WF Hnorm Htransl Hcheck Hparcb.
  unfold check_parcborparcb' in Hcheck.
  rewrite forallb_forall in Hcheck.
  case_eq((fn_parcopycode tf) ! pc); try congruence; intros.
  specialize (Hcheck (pc, p)).
  exploit Hcheck; eauto.
  apply PTree.elements_correct; auto.
  intros Hcheck2.
  erewrite instructions_preserved in Hcheck2; eauto.
  clear Hcheck.
  flatten Hcheck2; go.
Qed.


Lemma used_parcnotjp_use_phi:
  forall f tf r pc,
  transl_function f = Errors.OK tf ->

  normalized_jp f ->
  check_parcborparcb' tf = true ->
  wf_ssa_function f ->
  use_parcopycode tf r pc ->
  ~ join_point pc f ->
  use_phicode f r pc.
Proof.
  intros f tf r pc Htrans Hnorm Hcheckparcborparcb' WF Huse Hjp.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans. flatten Htrans.
  inv Huse.
  exploit (check_parcborparcb'_correct f (get_tf s' f) pc);
    go.
  intros Hpc'.
  destruct Hpc' as [pc' Hpc'].
  destruct Hpc' as [Hinop Hpc'].
  destruct Hpc' as [Hphibpc | Hphibpc'].
  + contradict Hjp.
    rewrite <- exists_phib_iff in Hphibpc; go. go.
    apply fn_phicode_inv; auto.
  + assert(Hinoppc':
      exists succ, (CSSA.fn_code (get_tf s' f)) ! pc' =
        Some (Inop succ)).
    eapply cssa_fn_inop_in_jp; eauto.
    simpl in *.
    destruct Hinoppc' as [succ Hinoppc'].
    exploit (index_pred_instr_some (Inop pc')
      pc' f pc); go; intros Hindex.
    destruct Hindex as [k Hindex].
    inv SPEC.
    exploit (H1 pc' (Inop succ) k); eauto; intros.
    inv H0.
    rewrite exists_phib_iff_none in H5; go. go.
    {
      exploit index_pred_some_nth; eauto; intros. 
      unfold successors_list in H0.
      unfold node in *.
      rewrite H6 in H0.
      congruence.
    }
    assert(EQ: pred = pc).
    eapply index_preds_pc_inj; eauto.
    rewrite EQ in *.
    assert(EQ2: parcb0 = parcb) by go.
    rewrite EQ2 in *.
    assert(
      exists args dst',
        In (Iphi args dst') phib /\
        nth_error args k = Some r).
    eapply parcbsrc_is_phibarg; eauto.
    destruct H0 as [args [dst' [Hin Hnth]]].
    go.
Qed.

Lemma NoDupdstphib_NoDupphib:
  forall phib,
  NoDup (map phib_dst phib) ->
  NoDup phib.
Proof.
  induction phib; intros.
  go.
  simpl in *. inv H.
  constructor; go.
  unfold not; intros.
  contradict H2.
  destruct a. eapply in_phib_dst_in; eauto.
Qed.

Lemma NoDupdstparcb_NoDupparcb:
  forall parcb,
  NoDup (map parc_dst parcb) ->
  NoDup parcb.
Proof.
  induction parcb; intros.
  go.
  simpl in *. inv H.
  constructor; go.
  unfold not; intros.
  contradict H2.
  destruct a. eapply parc_dst_in; eauto.
Qed.

Lemma twoargs_not_NoDup:
  forall phib args args' r,
  In (Iphi args r) phib ->
  In (Iphi args' r) phib ->
  args <> args' ->
  ~ NoDup (map phib_dst phib).
Proof.
  induction phib; intros.
  go.
  simpl in *.
  destruct H; destruct H0; go; unfold not; intros Hnodup.
  + inv Hnodup. simpl in *.
    contradict H4.
    eapply in_phib_dst_in; eauto.
  + inv Hnodup. simpl in *.
    contradict H4.
    eapply in_phib_dst_in; eauto.
  + inv Hnodup.
    contradict H5; go.
Qed.

Lemma twoparc_not_NoDup:
  forall parcb src src' r,
  In (Iparcopy src r) parcb ->
  In (Iparcopy src' r) parcb ->
  src <> src' ->
  ~ NoDup (map parc_dst parcb).
Proof.
  induction parcb; intros.
  go.
  simpl in *.
  destruct H; destruct H0; go; unfold not; intros Hnodup.
  + inv Hnodup. simpl in *.
    contradict H4.
    eapply parc_dst_in; eauto.
  + inv Hnodup. simpl in *.
    contradict H4.
    eapply parc_dst_in; eauto.
  + inv Hnodup.
    contradict H5; go.
Qed.

Lemma phib_plemaxreg :
  forall f tf r pc,
  transl_function f = Errors.OK tf ->
  wf_ssa_function f ->
  assigned_phi_spec (fn_phicode f) pc r ->
  Ple r (get_maxreg f).
Proof.
  intros until pc.
  intros Htrans WF Hassign.
  apply Ple_trans
    with (q := get_max_reg_in_phicode (fn_phicode f)).
  inv Hassign.
  apply Ple_trans
    with (q := get_max_reg_in_phib phiinstr).
  destruct H0.
  apply Ple_trans
    with (q := get_max_reg_in_phiins (Iphi x r)).
  apply max_reg_in_phi_dst.
  apply max_reg_in_phib_dst; auto.
  eapply max_reg_in_phicode; eauto.
  apply max_reg_correct_phicode.
Qed.

Lemma really_parcb_really_phib':
  forall maxreg k phib parcb phib' parcb',
  equiv_phib maxreg k phib parcb phib' parcb' ->
  forall src dst,
  In (Iparcopy src dst) parcb ->
  exists args dst',
  nth_error args k = Some dst /\
  In (Iphi args dst') phib'.
Proof.
  intros until parcb'.
  intro H.
  induction H; intros.
  inv H.
  inv H15. 
  + exists args'. exists dst'. split; go.
  + exploit IHequiv_phib; eauto. intros Hargs.
    destruct Hargs as [args0 [dst1 Hin]].
    destruct Hin.
    exists args0. exists dst1. split; go.
Qed.

Lemma nodup_phib_dst_twoins :
  forall phib args args' r,
  NoDup (map phib_dst phib) ->
  In (Iphi args r) phib ->
  In (Iphi args' r) phib ->
  args = args'.
Proof.
  induction phib; intros.
  inv H0.
  simpl in *.
  destruct H0; destruct H1.
  + go.
  + inv H.
    simpl in *.
    contradict H4.
    eapply in_phib_dst_in; eauto.
  + inv H.
    simpl in *.
    contradict H4.
    eapply in_phib_dst_in; eauto.
  + inv H.
    go.
Qed.

Lemma nodups_in_phib_nodup_in_args :
  forall phib,
  nodups_in_phib_spec phib ->
  forall r args args' dst dst',
  In r args ->
  In r args' ->
  In (Iphi args dst) phib ->
  In (Iphi args' dst') phib ->
  args = args' /\ dst = dst'.
Proof.
  intros phib H.
  induction H; intros; eauto.
  inv H1.
  inv H4; inv H5.
  + go.
  + replace args with args0 in *; go.
    replace dst with dst0 in *; go.
    exploit (H args' dst' r r); eauto.
    contradiction.
  + replace args with args' in *; go.
    replace dst with dst' in *; go.
    exploit (H args0 dst0 r r); eauto.
    contradiction.
  + go.
Qed.

Lemma Ple_maxreg_and_maxreg_Plt :
  forall (r : reg) maxreg,
  Ple r maxreg ->
  Plt maxreg r ->
  False.
Proof.
  intros.
  assert(Hpltsame: Plt r r).
  apply Ple_Plt_trans with (q := maxreg).
  go. go.
  contradict Hpltsame.
  apply Plt_strict.
Qed.

Lemma notassign_phi_and_parc:
  forall f tf r pc pc',
  transl_function f = Errors.OK tf ->

  (* validations *)
  normalized_jp f ->
  CSSA.block_nb_args tf ->
  check_parcbSome tf (CSSA.get_preds tf) = true ->
  check_parcb'Some tf = true ->
  check_fn_parcb_inop tf = true ->
  check_fn_parcbjp tf = true ->
  check_parcborparcb' tf = true ->
  check_phicode_for_dups_in_phib tf = true ->

  wf_ssa_function f ->
  assigned_phi_spec (CSSA.fn_phicode tf) pc r ->
  assigned_parcopy_spec (CSSA.fn_parcopycode tf) pc' r ->
  False.
Proof.
  intros f tf r pc pc' Htrans
    Hnorm Hblock_nb_args HparcbSome Hparcb'Some Hparcb_inop Hparcbjp
    Hparcborparcb' Hnodups_in_phi
    WF.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans.
  unfold init_state in *.

  exploit mfold_copy_node_correct_more; eauto.
  assert (RWinitreg: next_fresh_reg s = Pos.succ (get_maxreg f))
    by go.
  rewrite RWinitreg. simpl.
  apply Plt_succ.
  flatten Eq.
  assert(Hnorepet: list_norepet (map fst (PTree.elements (fn_code f)))).
  apply PTree.elements_keys_norepet.
  apply list_norepet_NoDup; auto.
  intros Hchain.
  exploit chained_intervals_disjoint; eauto; intros Hdisjointphis.

  intros; simpl in *.
  unfold not; intros.
  exploit (check_parcborparcb'_correct f (get_tf s' f) pc');
    eauto.
  inv H1; go.
  intros Hpc'0.
  destruct Hpc'0 as [pc'0 [Hinop Hphicode]].
  destruct Hphicode as [Hphibpc | Hphibpc'].
  {
    case_eq(peq pc pc'); intros.
    - rewrite e in *.
      exploit assigned_parcjp_assigned_phi; eauto.
      inv H0.
      assert((CSSA.fn_phicode (get_tf s' f)) ! pc' <> None)
        by go.
      rewrite <- exists_phib_iff in H0; go.
      apply fn_phicode_inv; auto.
      intros Hassign.
      exploit assigned_phi_pltmaxreg_r; eauto; intros.
      assert(Ple  r (get_maxreg f)).
      eapply phib_plemaxreg; eauto.
      eapply Ple_maxreg_and_maxreg_Plt; eauto.
    - simpl in *.
      exploit assigned_phi_pltmaxreg_r; eauto; intros.
      assert(Ple r (get_maxreg f)).
      exploit assigned_parcjp_assigned_phi; eauto.
      apply fn_phicode_inv; go.
      rewrite exists_phib_iff; go. simpl. go.
      intros Hassignphi.
      eapply phib_plemaxreg; eauto.
      eapply Ple_maxreg_and_maxreg_Plt; eauto.
  }
  case_eq(peq pc'0 pc); intros.
  - rewrite e in *.
    inv SPEC; simpl in *.
    assert(exists succ, (CSSA.fn_code (get_tf s' f)) ! pc =
      Some (Inop succ)).
    eapply cssa_fn_inop_in_jp; go.
    destruct H3 as [succ Hinoppc'].
    exploit (index_pred_instr_some (Inop pc)
      pc f pc'); go; intros Hindex.
    destruct Hindex as [k Hindex].
    exploit (H4 pc (Inop succ) k); eauto; intros.
    inv H3.
    rewrite exists_phib_iff_none in H8; go. go.
    {
      exploit index_pred_some_nth; eauto; intros. 
      unfold successors_list in H3.
      unfold node in *.
      rewrite H9 in H3.
      congruence.
    }
    inv H0. inv H1.
    destruct H15 as [args Hinphib].
    destruct H16 as [src Hinparcb].
    assert(EQphibs: phiinstr = phib') by go.
    assert(Hpreds: pred = pc').
    eapply index_preds_pc_inj; eauto.
    rewrite Hpreds in *.
    assert(EQparcbs: parcb0 = parcb) by go.
    rewrite EQphibs in *.
    rewrite EQparcbs in *.
    assert(Hin:
      exists args' dst',
      nth_error args' k = Some r /\
      In (Iphi args' dst') phib').
    exploit equiv_phib_spec_correct; eauto; intros.
    eapply really_parcb_really_phib'; go.
    destruct Hin as [args' [dst' [Hnth Hin]]].
    case_eq(peq dst' r); intros.
    + rewrite e in *.
      assert(EQargs: args = args').
      {
        exploit (no_dups_in_phib_dst phib'); eauto.
        exploit check_phicode_for_dups_in_phib_correct; eauto.
        intros Hnodup.
        eapply nodup_phib_dst_twoins; eauto.
      }
      rewrite EQargs in *.
      assert(Hinrargs': In r args').
      eapply nth_In_reg; eauto.
      assert(Hnodup: NoDup (r :: args')).
      exploit check_phicode_for_dups_in_phib_correct; eauto.
      intros Hnodups.
      eapply nodups_in_phib_nodups_in_phi; eauto.
      inv Hnodup.
      contradiction.
    + exploit equiv_phib_spec_correct; eauto.
      intros Hequiv_phib.
      assert(Hinrargs': In r args').
      eapply nth_In_reg; eauto.
      exploit check_phicode_for_dups_in_phib_correct; eauto.
      intros.
      contradict Hinrargs'.
      eapply not_in_dst_and_args; eauto.
  - inv H0. inv H1.
    destruct H3 as [args1 Hin1].
    destruct H4 as [src Hin2].
    case_eq((st_phicode s') ! pc'0); go; intros phib Hphib.
    assert(In pc (filter (has_really_phiblock f) l)).
    { flatten Eq. eapply In_has_really_phiblock_filter; eauto. }

    inv SPEC; simpl in *.
    assert(exists succ, (CSSA.fn_code (get_tf s' f)) ! pc'0 =
      Some (Inop succ)).
    eapply cssa_fn_inop_in_jp; go.
    destruct H4 as [succ Hinoppc'].
    exploit (index_pred_instr_some (Inop pc'0)
      pc'0 f pc'); go; intros Hindex.
    destruct Hindex as [k Hindex].
    exploit (H5 pc'0 (Inop succ) k); eauto; intros.
    inv H4.
    rewrite exists_phib_iff_none in H9; go. go.
    {
      exploit index_pred_some_nth; eauto; intros. 
      unfold successors_list in H4.
      unfold node in *.
      rewrite H10 in H4.
      congruence.
    }
    assert(Hin:
      exists args dst',
      nth_error args k = Some r /\
      In (Iphi args dst') phib').
    assert(Hpreds: pred = pc').
    eapply index_preds_pc_inj; eauto.
    assert(EQparcbs: parcb0 = parcb) by go.
    rewrite EQparcbs in *.
    exploit equiv_phib_spec_correct; eauto; intros.
    eapply really_parcb_really_phib'; go.
    destruct Hin as [args [dst' Hin]].
    destruct Hin as [Hnth Hin].
    assert(In pc'0 (filter (has_really_phiblock f) l)).
    flatten Eq.
    eapply In_has_really_phiblock_filter; eauto.
     
    assert(disjoint_phis (st_phicode s') pc pc'0).
    eapply chained_disjoint_phis_correct; eauto.
    inv H16.
    assert(r <> r).
    assert(EQphibs: phiinstr = phib1) by go.
    assert(EQphibs': phib = phib'0) by go.
    rewrite EQphibs in *.
    rewrite EQphibs' in *.
    specialize (H19 args1 args r dst' r r).
    apply H19; go.
    congruence.
Qed.

Lemma no_successive_jp :
  forall f pc pc',
  wf_ssa_function f ->
  normalized_jp f ->
  join_point pc f ->
  join_point pc' f ->
  (fn_code f) ! pc = Some (Inop pc') ->
  False.
Proof.
  intros until pc'.
  intros WF Hnorm jp_pc jp_pc' Hinop.
  assert((fn_phicode f) ! pc = None).
  assert(HInpreds: In pc (get_preds f) !!! pc').
  apply make_predecessors_correct_1
    with (instr := Inop pc').
  auto. go.
  unfold successors_list in HInpreds.
  flatten HInpreds.
  unfold normalized_jp in Hnorm.
  apply Hnorm with (pc := pc')
    (preds := (get_preds f) !!! pc'); try congruence.
  apply fn_phicode_inv; auto.
  unfold successors_list. flatten.
  unfold successors_list. flatten.
  auto.
  inv HInpreds.
  assert((fn_phicode f) ! pc <> None).
  apply fn_phicode_inv; auto.
  congruence.
Qed.

Lemma nodups_in_phib_nodups_in_args :
  forall phib,
  nodups_in_phib_spec phib -> 
  forall args dst,
  In (Iphi args dst) phib -> 
  NoDup args.
Proof.
  intros phib H.
  induction H; intros; go.
  simpl in *.
  destruct H2; go.
  inv H0; go.
Qed.

Lemma nodups_args_nth_same_k :
  forall args k k' (r : reg),
  NoDup args ->
  nth_error args k = Some r ->
  nth_error args k' = Some r ->
  k = k'.
Proof.
  induction args; intros.
  destruct k; destruct k'; simpl in *;
    unfold Specif.error in *; congruence.
  destruct k; destruct k'; simpl in *;
    unfold Specif.error in *;
    unfold value in *; try congruence.
  + assert(In r args).
    eapply nth_In_reg; eauto.
    inv H; go.
  + assert(In r args).
    eapply nth_In_reg; eauto.
    inv H; go.
  + inv H. assert(k = k') by go.
    go.
Qed.

Lemma wf_unique_def :
  forall f tf,
  transl_function f = Errors.OK tf ->
  normalized_jp f ->
  CSSA.block_nb_args tf ->

  (* validations *)
  check_parcbSome tf (CSSA.get_preds tf) = true ->
  check_parcb'Some tf = true ->
  check_fn_parcb_inop tf = true ->
  check_fn_parcbjp tf = true ->
  check_parcborparcb' tf = true ->
  check_phicode_for_dups_in_phib tf = true ->

  wf_ssa_function f ->
  CSSA.unique_def_spec tf.
Proof.
  intros f tf Htrans
    Hnorm Hblock_nb_args HparcbSome Hparcb'Some Hparcb_inop Hparcbjp
    Hparcborparcb' Hphibnodups
    WF.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans.
  unfold init_state in *.

  exploit mfold_copy_node_correct_more; eauto.
  assert (RWinitreg: next_fresh_reg s = Pos.succ (get_maxreg f)) by go.
  rewrite RWinitreg. simpl.
  apply Plt_succ.
  flatten Eq.
  assert(Hnorepet: list_norepet (map fst (PTree.elements (fn_code f)))).
  apply PTree.elements_keys_norepet.
  apply list_norepet_NoDup; auto.
  intros Hchain.
  exploit chained_intervals_disjoint; eauto; intros Hdisjointphis.
  repeat split; auto.
  + erewrite instructions_preserved; eauto.
    induction WF. induction fn_ssa. specialize (H r pc pc'). intuition.
  + intros.
    inv H. inv H0.
    destruct H2 as [args1 Hin1].
    destruct H3 as [args2 Hin2].
    assert(In pc (filter (has_really_phiblock f) l)).
    { flatten Eq. eapply In_has_really_phiblock_filter; eauto. }
    assert(In pc' (filter (has_really_phiblock f) l)).
    { flatten Eq. eapply In_has_really_phiblock_filter; eauto. }
    case_eq(peq pc pc'); go. intros.
    assert(disjoint_phis (st_phicode s') pc pc').
    eapply chained_disjoint_phis_correct; eauto.
    inv H4.
    assert(r <> r).
    assert(EQphibs: phiinstr = phib) by go.
    assert(EQphibs': phiinstr0 = phib') by go.
    rewrite EQphibs in *.
    rewrite EQphibs' in *.
    eapply H7; eauto.
    congruence.
  + intros. simpl in *.
    exploit (check_parcborparcb'_correct f (get_tf s' f) pc);
      go.
    inv H; go.
    exploit (check_parcborparcb'_correct f (get_tf s' f) pc');
      go.
    inv H0; go.
    intros Hpc Hpc'.
    destruct Hpc as [pc0 [Hinop Hphicode]].
    destruct Hpc' as [pc'0 [Hinop' Hphicode']].
    destruct Hphicode as [Hphibpc | Hphibpc0];
    destruct Hphicode' as [Hphibpc' | Hphibpc'0].
    - assert(Hassign: assigned_phi_spec (fn_phicode f) pc r).
      eapply assigned_parcjp_assigned_phi; eauto.
      apply fn_phicode_inv; auto.
      rewrite exists_phib_iff; go. go.
      assert(Hassign': assigned_phi_spec (fn_phicode f) pc' r).
      eapply assigned_parcjp_assigned_phi; eauto.
      apply fn_phicode_inv; auto.
      rewrite exists_phib_iff; go. go.
      induction WF.
      inv fn_ssa.
      specialize (H1 r pc pc').
      intuition.
    - assert(Plt (get_maxreg f) r).
      { apply assigned_parc_pltmaxreg_notjp
          with (tf := get_tf s' f) (pc := pc); eauto.
        unfold not; intros.
        assert(Hjp: join_point pc'0 f).
        apply fn_phicode_inv; auto.
        rewrite exists_phib_iff; go. go.
        apply no_successive_jp
          with (f := f) (pc := pc) (pc' := pc'0); eauto.
      }
      exploit assigned_parcjp_assigned_phi; eauto.
      apply fn_phicode_inv; auto.
      rewrite exists_phib_iff; go. go.
      intros Hassign.
      assert(Ple r (get_maxreg f)).
      eapply phib_plemaxreg; eauto.
      exfalso.
      eapply Ple_maxreg_and_maxreg_Plt; eauto.
    - assert(Plt (get_maxreg f) r).
      { apply assigned_parc_pltmaxreg_notjp
          with (tf := get_tf s' f) (pc := pc'); eauto.
        unfold not; intros.
        assert(Hjp: join_point pc0 f).
        apply fn_phicode_inv; auto.
        rewrite exists_phib_iff; go. go.
        apply no_successive_jp
          with (f := f) (pc := pc') (pc' := pc0); eauto.
      }
      assert(Hassign: assigned_phi_spec (fn_phicode f) pc r).
      eapply assigned_parcjp_assigned_phi; eauto.
      apply fn_phicode_inv; auto.
      rewrite exists_phib_iff; go. go.
      assert(Ple r (get_maxreg f)).
      eapply phib_plemaxreg; eauto.
      exfalso.
      eapply Ple_maxreg_and_maxreg_Plt; eauto.
    - inv SPEC; simpl in *. 
      assert(Hinoppc0:
        exists succ, (CSSA.fn_code (get_tf s' f)) ! pc0 =
          Some (Inop succ)).
      eapply cssa_fn_inop_in_jp; go.
      destruct Hinoppc0 as [succ Hinoppc0].
      assert(Hinoppc'0:
        exists succ', (CSSA.fn_code (get_tf s' f)) ! pc'0 =
          Some (Inop succ')).
      eapply cssa_fn_inop_in_jp; go.
      destruct Hinoppc'0 as [succ' Hinoppc'0].
      exploit (index_pred_instr_some (Inop pc0)
        pc0 f pc'); go; intros Hindexpc'.
      destruct Hindexpc' as [k' Hindexpc'].
      exploit (index_pred_instr_some (Inop pc'0)
        pc'0 f pc); go; intros Hindexpc.
      destruct Hindexpc as [k Hindexpc].
      exploit (H3 pc0 (Inop succ) k'); eauto.
      intros Hcssak'.
      exploit (H3 pc'0 (Inop succ') k); eauto.
      intros Hcssak.
      inv Hcssak'.
      rewrite exists_phib_iff_none in H2; go. go.
      {
        exploit (index_pred_some_nth pc0); eauto; intros. 
        unfold successors_list in H9.
        unfold node in *.
        rewrite H7 in H9.
        congruence.
      }
      inv Hcssak.
      rewrite exists_phib_iff_none in H13; go. go.
      {
        exploit (index_pred_some_nth pc'0); eauto; intros. 
        unfold successors_list in H16.
        unfold node in *.
        rewrite H14 in H16.
        congruence.
      }
      assert(Eqpcpred0: pred0 = pc).
      eapply index_preds_pc_inj; eauto.
      rewrite Eqpcpred0 in *.
      assert(Eqpc'pred: pred = pc').
      eapply index_preds_pc_inj; eauto.
      rewrite Eqpc'pred in *.
      inv H. inv H0.
      assert(EQparcbs1: parcb1 = parcb0) by go.
      rewrite EQparcbs1 in *.
      assert(EQparcbs2: parcb2 = parcb) by go.
      rewrite EQparcbs2 in *.
      destruct H21 as [src Hin].
      destruct H22 as [src' Hin'].
      assert(Hinphib'0: exists args' dst',
        nth_error args' k = Some r /\
        In (Iphi args' dst') phib'0).
      eapply equiv_phib_spec_parcbdst_inphib'; eauto.
      assert(Hinphib': exists args' dst',
        nth_error args' k' = Some r /\
        In (Iphi args' dst') phib').
      eapply equiv_phib_spec_parcbdst_inphib'; eauto.
      destruct Hinphib'0 as [args' Hinphib'0].
      destruct Hinphib'0 as [dst' Hinphib'0].
      destruct Hinphib'0 as [Hnth Hinphib'0].
      destruct Hinphib' as [args'' Hinphib'].
      destruct Hinphib' as [dst'' Hinphib'].
      destruct Hinphib' as [Hnth' Hinphib'].

      assert(EQpcs: pc'0 = pc0).
      {
        assert(In pc0 (filter (has_really_phiblock f) l)).
        { flatten Eq. eapply In_has_really_phiblock_filter; eauto. }
        assert(In pc'0 (filter (has_really_phiblock f) l)).
        { flatten Eq. eapply In_has_really_phiblock_filter; eauto. }
        case_eq(peq pc'0 pc0); go. intros.
        assert(disjoint_phis (st_phicode s') pc0 pc'0).
        eapply chained_disjoint_phis_correct; eauto.
        inv H23.
        assert(r <> r).
        assert(EQphibs: phib1 = phib') by go.
        assert(EQphibs': phib'1 = phib'0) by go.
        rewrite EQphibs in *.
        rewrite EQphibs' in *.
        eapply H26; eauto.
        congruence.
      }
      rewrite EQpcs in *.
      assert(EQphibs: phib'0 = phib') by go.
      rewrite EQphibs in *.
      exploit check_phicode_for_dups_in_phib_correct; eauto.
      intros.
      assert(Hinrargs': In r args').
      eapply nth_In_reg; eauto.
      assert(Hinrargs'': In r args'').
      eapply nth_In_reg; eauto.
      assert(Heqargsdst:
        args' = args'' /\ dst' = dst'').
      eapply nodups_in_phib_nodup_in_args; eauto.
      destruct Heqargsdst as [Heqargs Heqdst].
      rewrite <- Heqargs in *.
      exploit nodups_in_phib_nodups_in_args; eauto.
      intros Hnodups.
      assert(Heqks: k = k').
      eapply nodups_args_nth_same_k; eauto.
      rewrite Heqks in *.
      eapply index_preds_pc_inj; eauto.
  + intros. simpl in *.
    unfold not; intros.
    exploit assigned_phi_pltmaxreg_r; eauto; intros.
    assert(Ple r (get_maxreg f)).
    eapply assigned_code_plemaxreg; eauto.
    eapply Ple_maxreg_and_maxreg_Plt; eauto.
  + intros; simpl in *.
    assert(Ple r (get_maxreg f)).
    eapply assigned_code_plemaxreg; eauto; intros.
    assert(Hjpnotjp: join_point pc' f \/ ~ join_point pc' f).
    apply classic.
    unfold not; intros Hnotparc.
    destruct Hjpnotjp as [Hjp | Hnotjp].
    - exploit assigned_parcjp_assigned_phi; eauto; intros.
      induction WF. induction fn_ssa.
      specialize (H r pc' pc). intuition.
    - assert(Plt (get_maxreg f) r).
      eapply assigned_parc_pltmaxreg_notjp; eauto.
      eapply Ple_maxreg_and_maxreg_Plt; eauto.
  + intros; simpl in *.
    unfold not; intros.
    exploit assigned_phi_pltmaxreg_r; eauto; intros.
    assert(Ple r (get_maxreg f)).
    eapply assigned_code_plemaxreg; eauto.
    eapply Ple_maxreg_and_maxreg_Plt; eauto.
  + intros; simpl in *.
    unfold not; intros.
    eapply notassign_phi_and_parc; eauto.
  + intros; simpl in *.
    unfold not; intros Hnotcode.
    assert(Ple r (get_maxreg f)).
    eapply assigned_code_plemaxreg; eauto; intros.
    assert(Hjpnotjp: join_point pc f \/ ~ join_point pc f).
    apply classic.
    destruct Hjpnotjp as [Hjp | Hnotjp].
    - exploit assigned_parcjp_assigned_phi; eauto; intros.
      induction WF. induction fn_ssa.
      specialize (H r pc pc'). intuition.
    - assert(Plt (get_maxreg f) r).
      eapply assigned_parc_pltmaxreg_notjp; eauto.
      eapply Ple_maxreg_and_maxreg_Plt; eauto.
  + intros; simpl in *.
    unfold not; intros.
    eapply notassign_phi_and_parc; eauto.
  + intros; simpl in *.
    inv SPEC; simpl in *.
    assert(exists succ, (CSSA.fn_code (get_tf s' f)) ! pc =
      Some (Inop succ)).
    eapply cssa_fn_inop_in_jp; go.
    destruct H1 as [succ Hinop].
    exploit (H2 pc (Inop succ) 0); eauto; intros.
    inv H1; go.
    rewrite exists_phib_iff_none in H6; go. go.
    {
      simpl in H8. flatten H8; simpl in *.
      assert(Hjp: join_point pc f). rewrite fn_phicode_inv in *; go.
      inv Hjp.
      unfold node in *.
      assert(Hnill: nil = l) by go.
      rewrite <- Hnill in Hl. simpl in Hl. go.
      
    }
    exploit equiv_phib_spec_correct; eauto; intros.
    exploit equiv_phib_nodups_phib'_dst; eauto; intros.
    assert(Heqphibs: phiinstr = phib') by go.
    rewrite Heqphibs in *.
    apply NoDupdstphib_NoDupphib; auto.
  + intros. simpl in *.
    inv SPEC; simpl in *.
    assert(exists succ, (CSSA.fn_code (get_tf s' f)) ! pc =
      Some (Inop succ)).
    eapply cssa_fn_inop_in_jp; go.
    destruct H3 as [succ Hinop].
    exploit (H4 pc (Inop succ) 0); eauto; intros.
    inv H3.
    rewrite exists_phib_iff_none in H8; go. go.
    {
      simpl in H10. flatten H10; simpl in *.
      assert(Hjp: join_point pc f). rewrite fn_phicode_inv in *; go.
      inv Hjp.
      unfold node in *.
      assert(Hnill: nil = l) by go.
      rewrite <- Hnill in Hl. simpl in Hl. go.
      
    }
    exploit equiv_phib_spec_correct; eauto; intros.
    exploit equiv_phib_nodups_phib'_dst; eauto; intros.
    apply Peirce; intros.
    assert(RW: phiinstr = phib') by go.
    rewrite RW in *.
    contradict H15.
    apply twoargs_not_NoDup
      with (args := args) (args' := args') (r := r); auto.
  + simpl in *.
    exploit (check_parcborparcb'_correct f (get_tf s' f) pc);
      go.
    intros Hpc'.
    destruct Hpc' as [pc' [Hinop Hphicode]].
    destruct Hphicode as [Hphibpc | Hphibpc'].
    - inv SPEC; simpl in *.
      exploit (H2 pc (Inop pc') 0); eauto; intros.
      inv H1.
      rewrite exists_phib_iff_none in H6; go. go.
      {
        simpl in H8. flatten H8; simpl in *.
        assert(Hjp: join_point pc f). rewrite fn_phicode_inv in *; go.
        inv Hjp.
        unfold node in *.
        assert(Hnill: nil = l) by go.
        rewrite <- Hnill in Hl. simpl in Hl. go.
        
      }
      exploit equiv_phib_spec_correct; eauto; intros.
      exploit equiv_phib_nodups_parcb'_dst; eauto; intros.
      assert(EQ: parcb = parcb') by go.
      rewrite EQ in *.
      apply NoDupdstparcb_NoDupparcb; auto.
    - inv SPEC; simpl in *.
      assert(exists succ, (CSSA.fn_code (get_tf s' f)) ! pc' =
        Some (Inop succ)).
      eapply cssa_fn_inop_in_jp; go.
      destruct H1 as [succ Hinoppc'].
      exploit (index_pred_instr_some (Inop pc')
        pc' f pc); go; intros Hindex.
      destruct Hindex as [k Hindex].
      exploit (H2 pc' (Inop succ) k); eauto; intros.
      inv H1.
      rewrite exists_phib_iff_none in H6; go. go.
      {
        exploit index_pred_some_nth; eauto; intros. 
        unfold successors_list in H1.
        unfold node in *.
        rewrite H7 in H1.
        congruence.
      }
      exploit equiv_phib_spec_correct; eauto; intros.
      exploit equiv_phib_nodups_parcb_dst; eauto; intros.
      assert(Eqpcpred: pred = pc).
      eapply index_preds_pc_inj; eauto.
      rewrite Eqpcpred in *.
      assert(EQ: parcb0 = parcb) by go.
      rewrite EQ in *.
      apply NoDupdstparcb_NoDupparcb; auto.
  + intros.
    exploit (check_parcborparcb'_correct f (get_tf s' f) pc);
      eauto.
    go.
    intros Hpc'.
    destruct Hpc' as [pc' [Hinop Hphicode]].
    destruct Hphicode as [Hphibpc | Hphibpc'].
    - inv SPEC; simpl in *.
      exploit (H4 pc (Inop pc') 0); eauto; intros.
      inv H3.
      rewrite exists_phib_iff_none in H8; go. go.
      {
        simpl in H10. flatten H10; simpl in *.
        assert(Hjp: join_point pc f). rewrite fn_phicode_inv in *; go.
        inv Hjp.
        unfold node in *.
        assert(Hnill: nil = l) by go.
        rewrite <- Hnill in Hl. simpl in Hl. go.
        
      }
      exploit equiv_phib_spec_correct; eauto; intros.
      exploit equiv_phib_nodups_parcb'_dst; eauto; intros.
      apply Peirce; intros.
      contradict H15.
      assert(EQ: parcb = parcb') by go.
      rewrite EQ in *.
      apply twoparc_not_NoDup with
        (src := src) (src' := src') (r := dst); eauto.
    - inv SPEC; simpl in *.
      assert(exists succ, (CSSA.fn_code (get_tf s' f)) ! pc' =
        Some (Inop succ)).
      eapply cssa_fn_inop_in_jp; go.
      destruct H3 as [succ Hinoppc'].
      exploit (index_pred_instr_some (Inop pc')
        pc' f pc); go; intros Hindex.
      destruct Hindex as [k Hindex].
      exploit (H4 pc' (Inop succ) k); eauto; intros.
      inv H3.
      rewrite exists_phib_iff_none in H8; go. go.
      {
        exploit index_pred_some_nth; eauto; intros. 
        unfold successors_list in H3.
        unfold node in *.
        rewrite H9 in H3.
        congruence.
      }
      exploit equiv_phib_spec_correct; eauto; intros.
      exploit equiv_phib_nodups_parcb_dst; eauto; intros.
      apply Peirce; intros.
      contradict H15.
      assert(Eqpcpred: pred = pc).
      eapply index_preds_pc_inj; eauto.
      rewrite Eqpcpred in *.
      assert(EQ: parcb0 = parcb) by go.
      rewrite EQ in *.
      apply twoparc_not_NoDup with
        (src := src) (src' := src') (r := dst); eauto.
Qed.

Lemma wf_cssa_extrainv_1 :
  forall f tf,
  transl_function f = Errors.OK tf ->

  normalized_jp f ->
  wf_ssa_function f ->

  forall pc r,
  CSSA.join_point pc tf ->
  use_parcopycode tf r pc ->
  assigned_phi_spec (CSSA.fn_phicode tf) pc r.
Proof.
  intros f tf Htrans
    Hnorm WF.
  intros.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans.
  intros. inv SPEC. inv H0. simpl in *.
  assert(Hinop: exists succ,
    (CSSA.fn_code (get_tf s' f)) ! pc = Some (Inop succ)).
  eapply cssa_fn_inop_in_jp; go.
  simpl.
  assert(Hjp: join_point pc f) by
    (eapply no_new_joinpoints; eauto).
  rewrite fn_phicode_inv in Hjp; auto.
  assert(Hphib': (CSSA.fn_phicode (get_tf s' f)) ! pc <> None).
  rewrite <- exists_phib_iff; go.
  go.
  destruct Hinop as [succ Hinop].
  exploit (H3 pc (Inop succ) 0); eauto; intros.
  inv H0.
  - assert(Hjp: join_point pc f) by
      (eapply no_new_joinpoints; eauto).
    rewrite fn_phicode_inv in Hjp; auto.    
    congruence.
  - intros.
    unfold successors_list in H.
    assert(Hjp: join_point pc f) by
      (eapply no_new_joinpoints; eauto).
    induction Hjp.
    unfold node in *.
    assert(EQ: lpreds = l0) by go.
    rewrite EQ in *.
    destruct l0; go.
  - econstructor; eauto.
    assert(EQ: parcb = parcb') by go.
    rewrite EQ in *.
    eapply equiv_phib_parcb'src_phibdst'; eauto.
Qed.

Lemma wf_cssa_extrainv_2 :
  forall f tf,
  transl_function f = Errors.OK tf ->

  (* validations *)
  normalized_jp f ->
  wf_ssa_function f ->

  forall pc r,
  CSSA.use_phicode tf r pc ->
  assigned_parcopy_spec (CSSA.fn_parcopycode tf) pc r.
Proof.
  intros f tf Htrans
    Hnorm WF.
  intros.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans.
  intros. inv SPEC. inv H. simpl in *.
  assert(Hinop: exists succ,
    (CSSA.fn_code (get_tf s' f)) ! pc0 = Some (Inop succ)).
  eapply cssa_fn_inop_in_jp; go.
  destruct Hinop as [succ Hinop].
  exploit (H2 pc0 (Inop succ) k); eauto; intros.
  inv H.
  - rewrite exists_phib_iff_none in H1; go.
    simpl in *. go.
  - exploit index_pred_some_nth; eauto.
    intros.
    unfold successors_list in H.
    flatten H.
    unfold node in *.
    assert(EQ: lpreds = l0) by go.
    rewrite EQ in *.
    assert(nth_error l0 k = None); go.
    destruct k; simpl in *;
    unfold Specif.error in H; congruence.
  - assert(EQ: pred = pc).
    eapply index_preds_pc_inj; eauto.
    rewrite EQ in *.
    econstructor; eauto.
    assert(EQphibs: phib = phib') by go.
    rewrite EQphibs in *.
    eapply equiv_phib_phibarg_parcdst; eauto.
Qed.

Lemma assigned_phi_assigned_parcb':
  forall f tf,
  transl_function f = Errors.OK tf ->

  (* validations *)
  normalized_jp f ->
  wf_ssa_function f ->

  forall pc r,
  assigned_phi_spec (fn_phicode f) pc r ->
  assigned_parcopy_spec (CSSA.fn_parcopycode tf) pc r.
Proof.
  intros f tf Htrans
    Hnorm WF.
  intros.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans.
  intros. inv SPEC. inv H. simpl in *.
  unfold inop_in_jp in H5.
  exploit (H5 pc); eauto. congruence.
  intros.
  destruct H as [succ Hinop].
  exploit (H2 pc (Inop succ) 0); eauto; intros.
  inv H.
  - congruence.
  - intros.
    assert(Hjp: join_point pc f).
    apply fn_phicode_inv; auto. congruence.
    induction Hjp.
    unfold node in *.
    assert(EQ: lpreds = l0) by go.
    rewrite EQ in *.
    destruct l0; go.
    
  - econstructor; eauto.
    destruct H6.
    assert(EQ: phiinstr = phib) by go.
    rewrite EQ in *.
    eapply equiv_phib_phibdst_parcb'src; eauto.
Qed.

Lemma param_ple_maxreg :
  forall x f,
  In x (fn_params f) ->
  Ple x (get_maxreg f).
Proof.
  intros.
  unfold get_maxreg.
  apply Ple_trans with
    (Pos.max (get_max_reg_in_phicode (fn_phicode f))
      (max_reg_in_list (fn_params f))).
  apply Ple_trans with 
      (max_reg_in_list (fn_params f)).
  apply max_reg_in_list_correct; auto. 
  apply Pos.le_max_r.
  apply Pos.le_max_r.
Qed.

Lemma use_phib_ple_maxreg :
  forall f r pc,
  wf_ssa_function f ->
  use_phicode f r pc ->
  Ple r (get_maxreg f).
Proof.
  intros.
  inv H0.
  apply Ple_trans with (get_max_reg_in_phicode (fn_phicode f)).
  apply Ple_trans with (get_max_reg_in_phib phib).
  apply Ple_trans with (get_max_reg_in_phiins (Iphi args dst)).
  apply max_reg_in_phi_arg.
  eapply nth_In_reg; eauto.
  apply max_reg_in_phib_dst; auto.
  eapply max_reg_in_phicode; eauto.
  apply max_reg_correct_phicode.
Qed.

Lemma parcb_src_ple_maxreg :
  forall maxreg k phib parcb phib' parcb',
  equiv_phib_spec maxreg k phib parcb phib' parcb' ->
  forall src dst,
  In (Iparcopy src dst) parcb ->
  Ple src maxreg.
Proof.
  intros until parcb'.
  intros H. induction H; intros.
  inv H.
  simpl in *.
  destruct H9; go.
Qed.

Lemma cssa_def_code_def_code:
  forall f tf r pc,
  transl_function f = Errors.OK tf ->
  normalized_jp f ->
  wf_ssa_function f ->
  assigned_code_spec (CSSA.fn_code tf) r pc ->
  assigned_code_spec (fn_code f) r pc.
Proof.
  intros.
  unfold transl_function in H.
  flatten Htrans; simpl in *.
  inv H2; go.
Qed.

Lemma cssa_use_code_use_code:
  forall f tf r pc,
  transl_function f = Errors.OK tf ->
  normalized_jp f ->
  wf_ssa_function f ->
  CSSA.use_code tf r pc ->
  use_code f r pc.
Proof. 
  intros.
  unfold transl_function in H.
  flatten Htrans; simpl in *.
  inv H2; simpl in * ; go.
Qed.

Lemma cssa_ext_params_ext_params:
  forall f tf r,
  transl_function f = Errors.OK tf ->
  check_parcborparcb' tf = true ->
  normalized_jp f ->
  wf_ssa_function f ->
  CSSA.ext_params tf r ->
  ext_params f r.
Proof.
  intros f tf r Htrans Hcheckparcborparcb' Hnorm WF Hext.
  inv Hext.
  + unfold transl_function in Htrans.
    flatten Htrans.
    constructor 1. auto.
  + destruct H.
    constructor 2.
    - inv H.
      exploit cssa_use_code_use_code; eauto.
      intros. exists x. go.
      exploit wf_cssa_extrainv_2; eauto.
      intros. contradict H2. eauto.
      exploit (check_parcborparcb'_correct f tf x);
        eauto.
      inv H3; go.
      intros Hpc'.
      destruct Hpc' as [pc' [Hinop Hphicode]].
      destruct Hphicode as [Hphibpc | Hphibpc'].
      exploit wf_cssa_extrainv_1; eauto.
      eapply wf_fn_phicode_inv; eauto.
      intros.
      contradict H. eauto.
      exploit used_parcnotjp_use_phi; eauto.
      unfold not; intros.
      apply no_successive_jp with (f := f) (pc := x)
        (pc' := pc'); eauto.
      rewrite <- exists_phib_iff in Hphibpc'; eauto.
      apply fn_phicode_inv; auto.
      intros.
      exists x. go.
    - intros. unfold not; intros Hassignphi.
      exploit assigned_phi_assigned_parcb'; eauto.
      intros Hassign.
      contradict Hassign. eauto.
    - intros. unfold not; intros Hassigncode.
      contradict Hassigncode.
      unfold transl_function in Htrans. flatten Htrans. eauto.
Qed.

Lemma ext_params_ple_maxreg:
  forall f r,
  wf_ssa_function f ->
  ext_params f r ->
  Ple r (get_maxreg f).
Proof.
  intros.
  inv H0.
  + apply param_ple_maxreg; auto.
  + destruct H1.
    inv H0.
    - eapply use_code_plemaxreg; eauto.
    - eapply use_phib_ple_maxreg; eauto.
Qed.

Lemma cssa_cfg_cfg:
  forall f tf pc pc',
  transl_function f = Errors.OK tf ->
  cfg f pc pc' ->
  CSSA.cfg tf pc pc'.
Proof.
  intros.
  unfold transl_function in H.
  flatten H; simpl in *.
  inv H0; go.
Qed.

Lemma cssa_cfg_cfg_2:
  forall f tf pc pc',
  transl_function f = Errors.OK tf ->
  CSSA.cfg tf pc pc' ->
  cfg f pc pc'.
Proof.
  intros.
  unfold transl_function in H.
  flatten H; simpl in *.
  inv H0; go.
Qed.

Lemma cssa_cfg_star_cfg_star:
  forall f tf pc pc',
  transl_function f = Errors.OK tf ->
  (cfg f **) pc pc' ->
  (CSSA.cfg tf **) pc pc'.
Proof.
  intros.
  induction H0.
  + constructor.
    eapply cssa_cfg_cfg; eauto.
  + constructor 2.
  + constructor 3 with (y := y); auto.
Qed.

Lemma cssa_cfg_star_cfg_star_2:
  forall f tf pc pc',
  transl_function f = Errors.OK tf ->
  (CSSA.cfg tf **) pc pc' ->
  (cfg f **) pc pc'.
Proof.
  intros.
  induction H0.
  + constructor.
    eapply cssa_cfg_cfg_2; eauto.
  + constructor 2.
  + constructor 3 with (y := y); auto.
Qed.

Lemma cssa_reached_reached:
  forall f tf pc,
  transl_function f = Errors.OK tf ->
  reached f pc ->
  CSSA.reached tf pc.
Proof.
  intros.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in H.
  flatten H; simpl in *.
  induction H0.
  + constructor.
    eapply cssa_cfg_cfg; eauto.
  + constructor 2.
  + constructor 3 with (y := y).
    eapply IHclos_refl_trans1; eauto.
    eapply cssa_cfg_star_cfg_star; eauto.
Qed.

Lemma cssa_reached_reached_2:
  forall f tf pc,
  transl_function f = Errors.OK tf ->
  CSSA.reached tf pc ->
  reached f pc.
Proof.
  intros.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in H.
  flatten H; simpl in *.
  induction H0.
  + constructor.
    eapply cssa_cfg_cfg_2; eauto.
  + constructor 2.
  + constructor 3 with (y := y).
    eapply IHclos_refl_trans1; eauto.
    eapply cssa_cfg_star_cfg_star_2; eauto.
Qed.

Lemma cssa_path_path :
  forall f tf l pc pc',
  transl_function f = Errors.OK tf ->
  normalized_jp f ->
  wf_ssa_function f ->
  Dom.path (CSSA.cfg tf) (CSSA.exit tf) (fn_entrypoint f) pc l pc' ->
  Dom.path (cfg f) (exit f) (fn_entrypoint f) pc l pc'.
Proof.
  intros.
  induction H2.
  + constructor.
  + constructor 2
      with (s2 := s2).
    - inv STEP.
      { constructor.
        eapply cssa_reached_reached_2; eauto.
        replace (CSSA.entry tf) with (fn_entrypoint f).
        auto.
        unfold transl_function in H.
        flatten H; simpl; auto.
        eapply cssa_cfg_cfg_2; eauto. }
      { constructor 2.
        eapply cssa_reached_reached_2; eauto.
        replace (CSSA.entry tf) with (fn_entrypoint f).
        auto.
        unfold transl_function in H.
        flatten H; simpl; auto.
        unfold exit.
        unfold CSSA.exit in NOSTEP.
        erewrite instructions_preserved in NOSTEP; eauto.
      }
    - auto.
Qed.

Lemma cssa_dom_dom:
  forall f tf pc pc',
  transl_function f = Errors.OK tf ->
  normalized_jp f ->
  wf_ssa_function f ->
  dom f pc pc' ->
  CSSA.dom tf pc pc'.
Proof.
  intros.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in H.
  flatten Htrans; simpl in *.
  inv H2.
  + constructor.
  + constructor 2.
    eapply cssa_reached_reached; eauto.
    intros.
    exploit cssa_path_path; eauto.
Qed.


Section WF_CSSA.

Variable f : function.
Hypothesis WF : wf_ssa_function f.

Variable tf : CSSA.function.
Hypothesis Htrans : transl_function f = Errors.OK tf.

Lemma Hnorm : normalized_jp f.
Proof.
  unfold transl_function in * ; flatten Htrans ; boolInv.
  eapply normalisation_checker_correct; eauto.
Qed.
Hint Resolve Hnorm: core.

Lemma Hblock_nb_args : CSSA.block_nb_args tf.
Proof.
  unfold transl_function in * ; flatten Htrans ; boolInv.
  eapply check_nb_args_correct; eauto.
Qed.
Hint Resolve Hblock_nb_args: core.

Lemma HparcbSome : forall (phib : phiblock) (pc : positive),
                (CSSA.fn_phicode tf) ! pc = Some phib ->
                forall pred : positive,
                In pred (CSSA.get_preds tf) !!! pc ->
                (fn_parcopycode tf) ! pred <> None. 
Proof.
  unfold transl_function in * ; flatten Htrans ; boolInv.
  eapply check_parcbSome_correct; eauto.
Qed.
Hint Resolve HparcbSome: core.

Lemma Hparcb'Some :forall (phib : phiblock) (pc : positive),
                 (CSSA.fn_phicode tf) ! pc = Some phib ->
                 (fn_parcopycode tf) ! pc <> None.
Proof.
  unfold transl_function in * ; flatten Htrans ; boolInv.
  eapply check_parcb'Some_correct; eauto.
Qed.
Hint Resolve Hparcb'Some: core.

Lemma p_fn_entry : exists s : node,
                 (CSSA.fn_code tf) ! (CSSA.fn_entrypoint tf) =
                 Some (Inop s).
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  unfold transl_function in Htrans.
  flatten Htrans; simpl in *.
  apply fn_entry; auto. 
Qed.

Lemma p_fn_entry_pred : forall pc : positive,
                    ~ CSSA.cfg tf pc (CSSA.fn_entrypoint tf).
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  unfold transl_function in Htrans.
  flatten Htrans; simpl in *.
  inv WF. intros. unfold not; intros.
  contradict fn_entry_pred.
  unfold not; intros.
  specialize (H0 pc). apply H0.
  inv H. simpl in *. go.
Qed.

Lemma p_fn_no_parcb_at_entry : (fn_parcopycode tf) ! (CSSA.fn_entrypoint tf) =
                           None.
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  unfold transl_function in Htrans.
  flatten Htrans; simpl in *.
  rewrite andb_true_iff in Eq1.
  rewrite andb_true_iff in Eq1.
  destruct Eq1 as [[Check_jp Check_jpinop] Check_entry].
  unfold entry_point_not_jp_pred in Check_entry.
  flatten Check_entry.
Qed.

Lemma p_fn_phicode_inv : forall jp : positive,
                     CSSA.join_point jp tf <->
                     (CSSA.fn_phicode tf) ! jp <> None.
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  intros. eapply wf_fn_phicode_inv; eauto. 
Qed. 

Lemma p_fn_normalized : forall (jp : positive) (pc : positive),
                    CSSA.join_point jp tf ->
                    In jp (CSSA.succs tf pc) ->
                    (CSSA.fn_code tf) ! pc = Some (Inop jp).
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  intros.
  assert(join_point jp f).    
  { inv H. 
    erewrite instructions_preserved in Hpreds; go.
  }
  
  unfold CSSA.successors, successors_list in H0.
  rewrite PTree.gmap1 in H0.
  flatten H0; go.
  erewrite instructions_preserved ; go.
  exploit fn_normalized; eauto.
  erewrite instructions_preserved in Eq ; go.
  unfold successors_list, successors.
  rewrite PTree.gmap1.
  flatten. auto. 
Qed.

Lemma p_fn_inop_in_jp : forall pc : positive,
                    (CSSA.fn_phicode tf) ! pc <> None ->
                    exists succ : node,
                      (CSSA.fn_code tf) ! pc = Some (Inop succ).
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  intros. exploit cssa_fn_inop_in_jp; eauto.
Qed.

Hint Resolve normalisation_checker_correct: core.

Lemma p_fn_normalized_jp : forall (pc : positive) (preds : list positive),
                       (CSSA.fn_phicode tf) ! pc <> None ->
                       (CSSA.get_preds tf) ! pc = Some preds ->
                       forall pred : positive,
                       In pred preds -> (CSSA.fn_phicode tf) ! pred = None.
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans; simpl in *.
  intros.
  rewrite andb_true_iff in Eq1.
  rewrite andb_true_iff in Eq1.
  destruct Eq1 as [[Check_jp Check_jpinop] Check_entry].
  assert(Hphipreserved: (CSSA.fn_phicode (get_tf s' f)) ! pc
                        = (st_phicode s') ! pc) by go.
  rewrite <- Hphipreserved in H0.
  assert(Hphipreserved2: (CSSA.fn_phicode (get_tf s' f)) ! pred
                         = (st_phicode s') ! pred) by go.
  rewrite <- Hphipreserved2.
  rewrite <- exists_phib_iff in H0; go.
  - assert(Hnophipred: (fn_phicode f) ! pred = None)
    by(exploit normalisation_checker_correct; eauto).
    exploit exists_phib_iff; eauto. 
    intros truc.
    rewrite <- exists_phib_iff_none; eauto.
    Unshelve.
go.
Qed.
  
Lemma p_fn_parcbjp : forall (pc : positive) (pc' : node) (parcb : parcopyblock),
                 (fn_parcopycode tf) ! pc = Some parcb ->
                 (CSSA.fn_code tf) ! pc = Some (Inop pc') ->
                 ~ CSSA.join_point pc' tf -> CSSA.join_point pc tf.
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans; simpl in *.
  intros.
  eapply check_fn_parcbjp_correct; eauto.
  eapply normalisation_checker_correct; eauto.
  unfold transl_function in * ; flatten Hremembertrans; boolInv ; go.
  boolInv ; go.  
Qed.  

Lemma p_parcb_inop : forall pc : positive,
                 (fn_parcopycode tf) ! pc <> None ->
                 exists s : node, (CSSA.fn_code tf) ! pc = Some (Inop s).
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans; simpl in *.
  intros.
  case_eq((st_parcopycode s') ! pc); try congruence; intros.
  replace (fn_code f) with (CSSA.fn_code (get_tf s' f)) by go.
  eapply check_fn_parcb_inop_correct; eauto.
  unfold get_tf ; unfold transl_function in Hremembertrans ; 
  flatten Hremembertrans; boolInv ; go.
Qed.

Lemma p_fn_code_reached : forall (pc : positive) (ins : instruction),
                            (CSSA.fn_code tf) ! pc = Some ins ->
                            CSSA.reached tf pc.
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans; simpl in *.
  intros.
  eapply cfgeq_reached; eauto. intros.
  invh cfg. go.
Qed.  

Lemma p_fn_code_closed : forall (pc : positive) (pc' : node)
                       (instr : instruction),
                     (CSSA.fn_code tf) ! pc = Some instr ->
                     In pc' (successors_instr instr) ->
                     exists instr' : instruction,
                       (CSSA.fn_code tf) ! pc' = Some instr'.
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans; simpl in *.
  eapply fn_code_closed; eauto.
Qed.

Lemma p_fn_cssa : CSSA.unique_def_spec tf.
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans; boolInv ; simpl in *.
  eapply wf_unique_def; eauto. 
  eapply check_nb_args_correct; eauto.
Qed.

Lemma p_fn_cssa_params : forall x : reg,
                     In x (CSSA.fn_params tf) ->
                     (forall pc : node,
                      ~ assigned_code_spec (CSSA.fn_code tf) pc x) /\
                     (forall pc : node,
                      ~ assigned_phi_spec (CSSA.fn_phicode tf) pc x) /\
                     (forall pc : positive,
                      ~ assigned_parcopy_spec (fn_parcopycode tf) pc x).
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  assert(Hcheckjp : check_joinpoints f = true).
  {   unfold transl_function in Htrans.
      flatten Htrans; simpl in *.
      boolInv; auto.
  }
  unfold transl_function in Htrans.
  flatten Htrans; simpl in *.
  intros.
  repeat split; auto.
  - induction WF.
    specialize (fn_ssa_params x).
    intuition.
  - assert(Hple: Ple  x (get_maxreg f)).
    eapply param_ple_maxreg; eauto.
    intros. intro Hcont. 
    exploit assigned_phi_pltmaxreg_r; eauto; intros. eauto.
    eapply Ple_maxreg_and_maxreg_Plt; eauto.
  - intros. unfold not; intros. 
    boolInv. 
    exploit (check_parcborparcb'_correct f (get_tf s' f) pc);
      eauto.
    inv H; go.
    intros [pc' [Hinop Hphicode]].
    destruct Hphicode as [Hphibpc | Hphibpc'].
    {
      exploit assigned_parcjp_assigned_phi; eauto.
      rewrite <- exists_phib_iff in Hphibpc; eauto.
      apply SSA.fn_phicode_inv; auto.
      intros.
      induction WF.
      specialize (fn_ssa_params x).
      intuition eauto.
    }
    { assert(Hple: Ple  x (get_maxreg f)).
      eapply param_ple_maxreg; eauto.
      exploit assigned_parc_pltmaxreg_notjp; eauto.
      unfold not; intros.
      assert(join_point pc' f).
      rewrite <- exists_phib_iff in Hphibpc'; eauto.
      apply SSA.fn_phicode_inv; auto.
      apply no_successive_jp
      with (f := f) (pc := pc) (pc' := pc'); eauto; auto.
      intros.
      eapply Ple_maxreg_and_maxreg_Plt; eauto.
    }
Qed.

Hint Resolve ident_eq: core.

(* NOTE:
        + use-code def-code: ok => wf_ssa
        + use-[phib'|parcb'] def-code: def-[parcb|phib] => unique_def
        + use-[parcb] def-code: use-phib => wf_ssa
        + use-code def-[parcb|phib']: absurde (freshness)
        + use-code def-[parcb']: def-phib => wf_ssa
        + use-parcb def-[parcb|phib'] => freshness
        + use-parcb def-parcb': use-phib def-phib => wf_ssa
        + use-phib' def-parcb: ok si même point, sinon freshness
        + use-phib' def-phib': def-parcb => unique_def
        + use-phib' def-parcb': def-parcb => unique_def
        + use-parcb' def-parcb: def-phib' => unique_def
        + use-parcb' def-phib': ok si même point, sinon freshness
        + use-parcb' def-parcb'': def-phib' => unique_def
    *)
Lemma p_fn_strict : forall (x : reg) (u d : positive),
                CSSA.use tf x u -> CSSA.def tf x d -> CSSA.dom tf d u.
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans; boolInv ; simpl in *.
  intros; simpl in *.
  inv H0; inv H1.
  - exploit cssa_use_code_use_code; eauto; intros Huse.
    exploit cssa_ext_params_ext_params; eauto. intros Hext.
    eapply cssa_dom_dom; eauto.
    induction WF.
    eapply fn_strict; eauto.
    go. go.
  - exploit cssa_use_code_use_code; eauto; intros Huse.
    exploit cssa_def_code_def_code; eauto; intros Hdef.
    eapply cssa_dom_dom; eauto.
    induction WF.
    eapply fn_strict; eauto.
    go.
  - exploit cssa_use_code_use_code; eauto; intros Huse.
    assert(Ple x (get_maxreg f)).
    eapply use_code_plemaxreg; eauto.
    exploit assigned_phi_pltmaxreg_r; eauto; intros.
    exfalso.
    eapply Ple_maxreg_and_maxreg_Plt; eauto.
  - exploit (check_parcborparcb'_correct f (get_tf s' f) d); eauto.
    inv H0; go.
    intros Hpc'.
    destruct Hpc' as [pc' Hpc'].
    destruct Hpc' as [Hinop Hphicode].
    destruct Hphicode as [Hphicoded | Hphicodepc'].
    { exploit assigned_parcjp_assigned_phi; eauto.
      rewrite <- exists_phib_iff in Hphicoded; eauto.
      apply SSA.fn_phicode_inv; auto.
      intros Hassignphi.
      exploit cssa_use_code_use_code; eauto; intros Huse.
      eapply cssa_dom_dom; eauto.
      induction WF.
      eapply SSA.fn_strict; eauto.
      go.
    }
    {
      exploit cssa_use_code_use_code; eauto; intros Huse.
      assert(Ple x (get_maxreg f)).
      eapply use_code_plemaxreg; eauto.
      exploit assigned_parc_pltmaxreg_notjp; eauto.
      unfold not; intros.
      apply no_successive_jp
      with (f := f) (pc := d) (pc' := pc'); eauto; auto.
      rewrite <- exists_phib_iff in Hphicodepc'; eauto.
      apply SSA.fn_phicode_inv; auto.
      intros.
      exfalso.
      eapply Ple_maxreg_and_maxreg_Plt; eauto.
    }
  - exploit cssa_ext_params_ext_params; eauto; intros Hext.
    exploit wf_cssa_extrainv_2; eauto.
    intros. simpl in *.
    eapply Dom.entry_dom; eauto.
    {
      assert(reached f u0).
      { inv H1.
        exploit check_fn_parcb_inop_correct; eauto. simpl.
        intros [succ Hu0].
        induction WF.
        eapply SSA.fn_code_reached; eauto.
      }
      eapply cssa_reached_reached; eauto.
    }
  - exploit wf_cssa_extrainv_2; eauto. intros.
    exfalso. 
    exploit wf_unique_def; eauto. 
    eapply check_nb_args_correct; eauto. 
    intros Hunique.
    inv Hunique; simpl in *.
    specialize (H12 x d u0).
    intuition eauto.
  - exploit wf_cssa_extrainv_2; eauto.
    intros.
    exfalso.
    exploit wf_unique_def; eauto using check_nb_args_correct; intros Hunique.
    inv Hunique; simpl in *.
    specialize (H12 x d u0).
    intuition eauto.
  - exploit wf_cssa_extrainv_2; eauto.
    intros.
    case_eq(peq d u0); intros.
    { rewrite e in *.
      constructor.  }
    {
      exploit wf_unique_def; eauto using check_nb_args_correct; intros Hunique.
      inv Hunique; simpl in *.
      specialize (H13 x d u0).
      intuition eauto.
      contradiction.
    }
  - exploit (check_parcborparcb'_correct f (get_tf s' f) u0); eauto.
    inv H; go.
    intros Hpc'.
    destruct Hpc' as [pc' Hpc'].
    destruct Hpc' as [Hinop Hphicode].
    destruct Hphicode as [Hphicodeu0 | Hphicodepc'].
    {
      exploit wf_cssa_extrainv_1; eauto.
      rewrite <- exists_phib_iff in Hphicodeu0; eauto.
      eapply join_points_preserved; eauto.
      eapply fn_phicode_inv; eauto.
      intros Hassignphi.
      assert(Hple: Ple x (get_maxreg f)).
      eapply ext_params_ple_maxreg; eauto.
      eapply cssa_ext_params_ext_params; eauto.
      exploit assigned_phi_pltmaxreg_r; eauto; intros.
      exfalso.
      eapply Ple_maxreg_and_maxreg_Plt; eauto. }
    {
      assert(reached f u0).
      induction WF.
      eapply fn_code_reached; eauto.
      eapply cssa_dom_dom; eauto.
      apply Dom.entry_dom; auto.
    }

  - exploit (check_parcborparcb'_correct f (get_tf s' f) u0); eauto.
    inv H; go.
    intros Hpc'.
    destruct Hpc' as [pc' Hpc'].
    destruct Hpc' as [Hinop Hphicode].
    destruct Hphicode as [Hphicodeu0 | Hphicodepc'].
    { exploit wf_cssa_extrainv_1; eauto.
      rewrite <- exists_phib_iff in Hphicodeu0; eauto.
      assert(join_point u0 f).
      eapply fn_phicode_inv; eauto.
      eapply join_points_preserved; eauto.
      intros Hassign.
      exploit assigned_phi_pltmaxreg_r; eauto; intros.
      assert(Ple x (get_maxreg f)).
      eapply assigned_code_plemaxreg; eauto.
      exfalso.
      eapply Ple_maxreg_and_maxreg_Plt; eauto. }
    { exploit used_parcnotjp_use_phi; eauto.
      unfold not; intros.
      assert(join_point pc' f).
      rewrite <- exists_phib_iff in Hphicodepc'; eauto.
      eapply fn_phicode_inv; eauto.
      apply no_successive_jp
      with (f := f) (pc := u0) (pc' := pc'); eauto.
      intros Husephi.
      eapply cssa_dom_dom; eauto.
      induction WF.
      eapply fn_strict; eauto.
      go.  }
  - exploit (check_parcborparcb'_correct f (get_tf s' f) u0); eauto.
    inv H; go.
    intros Hpc'.
    destruct Hpc' as [pc' Hpc'].
    destruct Hpc' as [Hinop Hphicode].
    destruct Hphicode as [Hphicodeu0 | Hphicodepc'].
    { exploit wf_cssa_extrainv_1; eauto.
      rewrite <- exists_phib_iff in Hphicodeu0; eauto.
      eapply join_points_preserved; eauto.
      eapply fn_phicode_inv; eauto.
      intros Hassignphi.
      case_eq(peq d u0); intros.
      rewrite e in *. constructor.
      exploit wf_unique_def; eauto using check_nb_args_correct; intros Hunique.
      inv Hunique; simpl in *.
      specialize (H12 x d u0).
      intuition eauto.
      contradiction.  }
    { exploit used_parcnotjp_use_phi; eauto.
      unfold not; intros.
      rewrite <- exists_phib_iff in Hphicodepc'; eauto.
      assert(join_point pc' f).
      eapply fn_phicode_inv; eauto.
      apply no_successive_jp
      with (f := f) (pc := u0) (pc' := pc'); eauto.
      intros use_phi.
      assert(Hple: Ple x (get_maxreg f)).
      eapply use_phib_ple_maxreg; eauto.
      exploit assigned_phi_pltmaxreg_r; eauto; intros.
      exfalso.
      eapply Ple_maxreg_and_maxreg_Plt; eauto. }
  - exploit (check_parcborparcb'_correct f (get_tf s' f) u0); eauto.
    inv H; go.
    intros Hpc'.
    destruct Hpc' as [pc' Hpc'].
    destruct Hpc' as [Hinop Hphicode].
    destruct Hphicode as [Hphicodeu0 | Hphicodepc'].
    {
      exploit wf_cssa_extrainv_1; eauto.
      rewrite <- exists_phib_iff in Hphicodeu0; eauto.
      eapply join_points_preserved; eauto.
      eapply fn_phicode_inv; eauto.
      intros Hassignphi.
      exploit wf_unique_def; eauto using check_nb_args_correct; intros Hunique.
      inv Hunique; simpl in *.
      specialize (H1 x d u0).
      intuition eauto.
    }
    {
      exploit used_parcnotjp_use_phi; eauto.
      unfold not; intros.
      rewrite <- exists_phib_iff in Hphicodepc'; eauto.
      assert(join_point pc' f).
      eapply fn_phicode_inv; eauto.
      apply no_successive_jp
      with (f := f) (pc := u0) (pc' := pc'); eauto.
      intros use_phi.
      assert(Hple: Ple x (get_maxreg f)).
      eapply use_phib_ple_maxreg; eauto.
      exploit (check_parcborparcb'_correct f (get_tf s' f) d); eauto.
      inv H0; go.
      intros Hpc'0.
      destruct Hpc'0 as [pc'0 Hpc'0].
      destruct Hpc'0 as [Hinop0 Hphicode0].
      destruct Hphicode0 as [Hphicoded | Hphicodepc'0].
      + exploit assigned_parcjp_assigned_phi; eauto.
        rewrite <- exists_phib_iff in Hphicoded; eauto.
        eapply fn_phicode_inv; eauto.
        intros Hassignphi.
        eapply cssa_dom_dom; eauto.
        induction WF.
        eapply fn_strict; eauto.
        go.
      + exploit assigned_parc_pltmaxreg_notjp; eauto.
        unfold not; intros.
        apply no_successive_jp
        with (f := f) (pc := d) (pc' := pc'0); eauto.
        assert(Hphibnotnone:
                 (CSSA.fn_phicode (get_tf s' f)) ! pc'0 <> None)
          by go.
        rewrite <- exists_phib_iff in Hphibnotnone; eauto.
        apply fn_phicode_inv; auto.
        intros. exfalso.
        eapply Ple_maxreg_and_maxreg_Plt; eauto.
    }
Qed.  

Lemma p_fn_use_def_code : forall (x : reg) (pc : positive),
                      CSSA.use_code tf x pc ->
                      assigned_code_spec (CSSA.fn_code tf) pc x -> False.
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans; simpl in *.

  intros.
  induction WF.
  eapply SSA.fn_use_def_code; eauto.
  inv H0; go.
Qed.

Lemma p_fn_strict_use_parcb : forall (x : reg) (pc : positive),
                          use_parcopycode tf x pc ->
                          ~ assigned_parcopy_spec (fn_parcopycode tf) pc x.
Proof.
  exploit transl_function_spec_ok; eauto.
  eapply transl_function_charact; eauto.
  intros SPEC.
  assert(Hremembertrans: transl_function f = Errors.OK tf) by auto.
  unfold transl_function in Htrans.
  flatten Htrans; boolInv ; simpl in *.
  
  intros.
  unfold not; intros.
  exploit (check_parcborparcb'_correct f (get_tf s' f) pc); go.
  inv H; go.
  intros Hpc.
  destruct Hpc as [pc' Hpc].
  destruct Hpc as [Hinop Hphicode].
  destruct Hphicode as [Hphibpc | Hphibpc'].
  - exploit assigned_parcjp_assigned_phi; eauto.
    apply fn_phicode_inv; auto.
    rewrite exists_phib_iff; eauto.
    intros Hassign.
    assert(Ple  x (get_maxreg f)).
    eapply phib_plemaxreg; eauto.
    exploit wf_cssa_extrainv_1; eauto.
    eapply wf_fn_phicode_inv; eauto.
    intros Hassign_phib'.
    exploit assigned_phi_pltmaxreg_r; eauto; intros.
    eapply Ple_maxreg_and_maxreg_Plt; eauto.
  - exploit assigned_parc_pltmaxreg_notjp; eauto.
    unfold not; intros.
    rewrite <- exists_phib_iff in Hphibpc'; eauto.
    rewrite <- fn_phicode_inv in Hphibpc'; auto.
    apply no_successive_jp
    with (f := f) (pc := pc) (pc' := pc'); eauto; auto.
    intros Hplt.    
    intros. inv SPEC; simpl in *.

    assert(Hinoppc': exists succ,
                       (CSSA.fn_code (get_tf s' f)) ! pc' = Some (Inop succ)).
    eapply cssa_fn_inop_in_jp; go.
    destruct Hinoppc' as [succ Hinoppc'].
    exploit (index_pred_instr_some (Inop pc')
                                   pc' f pc); go; intros Hindex.
    destruct Hindex as [k Hindex].
    
    exploit (H13 pc' (Inop succ) k); eauto.
    intros.
    inv H12.
    rewrite exists_phib_iff_none in H17; go. go.
    {
      exploit index_pred_some_nth; eauto; intros. 
      unfold successors_list in H12.
      unfold node in *.
      rewrite H18 in H12.
      congruence.
    }
    invh use_parcopycode.
    assert(EQ: pred = pc).
    eapply index_preds_pc_inj; eauto.
    assert(EQ2: parcb0 = parcb) by go.
    rewrite EQ2 in *.
    assert(Ple  x (get_maxreg f)).
    eapply parcb_src_ple_maxreg; eauto.
    eapply Ple_maxreg_and_maxreg_Plt; eauto.
Qed.

Lemma p_fn_jp_use_parcb' : forall (x : reg) (pc : positive),
                       CSSA.join_point pc tf ->
                       use_parcopycode tf x pc ->
                       assigned_phi_spec (CSSA.fn_phicode tf) pc x.
Proof.
  intros. eapply wf_cssa_extrainv_1; eauto.
Qed.

Lemma p_fn_jp_use_phib : forall (x : reg) (pc : positive),
                     CSSA.use_phicode tf x pc ->
                     assigned_parcopy_spec (fn_parcopycode tf) pc x.
Proof.
  intros. eapply wf_cssa_extrainv_2; eauto.
Qed.

Lemma wf_cssa_tf : wf_cssa_function tf.
Proof.
  constructor; eauto.
  eapply p_fn_entry; eauto.
  eapply p_fn_entry_pred; eauto.
  eapply p_fn_no_parcb_at_entry; eauto.
  eapply p_fn_phicode_inv ; eauto.
  eapply p_fn_normalized; eauto.
  eapply p_fn_inop_in_jp; eauto.
  eapply p_fn_normalized_jp; eauto.
  eapply p_fn_parcbjp; eauto.
  eapply p_parcb_inop; eauto. 
  eapply p_fn_code_reached; eauto.
  eapply p_fn_code_closed; eauto.
  eapply p_fn_cssa ; eauto.
  eapply p_fn_cssa_params; eauto.
  eapply p_fn_strict ; eauto.
  eapply p_fn_use_def_code ; eauto.
  eapply p_fn_strict_use_parcb; eauto.
  eapply p_fn_jp_use_parcb'; eauto.
  eapply p_fn_jp_use_phib; eauto.
Qed.

End WF_CSSA.

Require Import Errors.

Lemma wf_cssa_tprog :
  forall prog tprog,
  wf_ssa_program prog ->
  match_prog prog tprog ->
  CSSA.wf_cssa_program tprog.
Proof.
  red. intros prog tprog WF_SSA MATCH. intros.
  red in  WF_SSA.
  inv MATCH.
  revert H0 H WF_SSA. clear.
  generalize (prog_defs tprog).
  induction 1; intros.
  - inv H.
  - inv H1.      
    + inv H. inv H2.
      { destruct f1 ; simpl in * ; try constructor; auto.
        * monadInv H5. 
          constructor.
          eapply wf_cssa_tf; eauto.
          destruct a1, g.
          exploit (WF_SSA (Internal f0) i); eauto.
          simpl in * ; eauto.
          left. inv H; simpl in *; auto. 
          intros. inv H1; auto.
          simpl in *. inv H.
        * monadInv H5.
          constructor.
      }
    + eapply IHlist_forall2; eauto.
Qed.
