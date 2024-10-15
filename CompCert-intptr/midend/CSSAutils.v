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
Require Import Kildall.
Require Import KildallComp.
Require Import DLib.
Require Import Classical.
Require Import Registers.
Unset Allow StrictProp.

Section WF_CSSA.

Variable f : function.
Hypothesis WF: wf_cssa_function f.
                              
Lemma wf_cssa_nodup_parcb : forall pc parcb, 
  (fn_parcopycode f) ! pc = Some parcb ->
  (NoDup (map parc_dst parcb)).
Proof.
  intros.
  exploit fn_cssa; eauto.
  unfold unique_def_spec; intros; repeat invh and.
  exploit H3; eauto; intros ; repeat invh and.
  generalize H4 H5. clear. 
  induction parcb; go.
  intros ; invh NoDup; simpl.
  constructor. 
  - intro Hcont. 
    destruct a; simpl in *. 
    eapply in_map_iff in Hcont; eauto. invh ex; invh and; subst.
    destruct x; simpl in *.
    assert (r = r0) by go; subst.
    congruence.
  - eapply IHparcb; eauto.
Qed.

Lemma wf_cssa_def_phi_code : forall r pc pc',
  assigned_phi_spec (fn_phicode f) pc r ->
  ~ assigned_code_spec (fn_code f) pc' r.
Proof.
  intros; intro.
  exploit fn_cssa; eauto.
  unfold unique_def_spec; intro; repeat invh and.
  specialize (H2 r pc pc'); eauto; intuition.
Qed.

Lemma wf_cssa_def_phi_parcopy : forall r pc pc',
  assigned_phi_spec (fn_phicode f) pc r ->
  assigned_parcopy_spec (fn_parcopycode f) pc' r ->
  False.
Proof.
  intros.
  exploit fn_cssa; eauto.
  unfold unique_def_spec; intro; repeat invh and.
  specialize (H2 r pc pc'); eauto; intuition.
Qed.

Lemma wf_cssa_def_code_parcopy : forall r pc pc',
  assigned_code_spec (fn_code f) pc r ->
  ~ assigned_parcopy_spec (fn_parcopycode f) pc' r.
Proof.
  intros; intro.
  exploit fn_cssa; eauto.
  unfold unique_def_spec; intro; repeat invh and.
  specialize (H2 r pc pc'); eauto; intuition.
Qed.

Lemma wf_cssa_def_parcopy_code : forall r pc pc',
  assigned_parcopy_spec (fn_parcopycode f) pc' r ->
  ~ assigned_code_spec (fn_code f) pc r.
Proof.
  intros; intro.
  exploit fn_cssa; eauto.
  unfold unique_def_spec; intro; repeat invh and.
  specialize (H2 r pc pc'); eauto; intuition.
Qed.

Lemma def_reached: forall x pc, 
    def f x pc -> reached f pc.
Proof.
  induction 1; intros.
  - go.
  - invh assigned_code_spec;
    eapply fn_code_reached; eauto.
  - invh assigned_phi_spec; invh ex.
    exploit (fn_inop_in_jp f WF pc) ; eauto.
    + go.
    + intros [s Hpc]; eapply fn_code_reached; eauto.
  - invh assigned_parcopy_spec; invh ex.
    exploit (parcb_inop f WF pc); eauto. go. 
    intros [s Hpc].
    eapply fn_code_reached; eauto.
Qed.

Lemma wf_cssa_norm_1 : forall pc phi,
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  (fn_phicode f) ! pc = Some phi  ->
  False.
Proof.
  intros pc phi CODE PHI.
  exploit (fn_inop_in_jp f WF pc); eauto; go.
  intros [succ Hnop]; congruence.
Qed.

Lemma fn_entrypoint_inv: 
  (exists i, (fn_code f) ! (fn_entrypoint f) = Some i) /\
  ~ join_point (fn_entrypoint f) f.
Proof.
  intros.
  exploit fn_entry ; eauto.
  intros (s & Hentry).
  split; eauto.

  intro Hcont. inv Hcont.
  destruct l. 
  - simpl in *. lia.
  - generalize (KildallComp.make_predecessors_correct2 (fn_code f) successors_instr).
    intros Hcont.
    exploit @KildallComp.make_predecessors_some; eauto.
    intros [ip Hip].
    specialize (Hcont p ip (fn_entrypoint f) Hip).
    eelim fn_entry_pred with (pc := p); eauto. econstructor ; eauto.
    apply Hcont.
    unfold successors_list, KildallComp.make_preds.
    rewrite Hpreds; auto.
Qed.

Lemma ext_params_1: forall x n, 
  ext_params f x ->
  ~ assigned_phi_spec (fn_phicode f) n x.
Proof.
  induction 1 ; go.
  exploit fn_cssa_params; eauto; intros. 
  repeat invh and ; go. 
Qed. 

Lemma unique_def_spec_def : forall x d1 d2,
  def f x d1 ->
  def f x d2 ->
  d1 <> d2 -> False.
Proof.
  intros.
  destruct (fn_cssa f) as [Hssa1 Hssa2]; auto.
  generalize (fn_entry f WF) ; intros. destruct H2 as [succ Hentry].
  generalize (fn_cssa_params f WF); intros Hparams.
  repeat invh def;
  repeat invh ext_params; 
  try solve 
      [ intuition
        exploit Hparams ; eauto; intros (HH & HH' & HH'') ; (exploit HH ; eauto)
       |exploit Hparams ; eauto; intros (HH & HH' & HH'') ; (exploit HH' ; eauto)
       |exploit Hparams ; eauto; intros (HH & HH' & HH'') ; (exploit HH'' ; eauto)
       | eelim H4; eauto
       | eelim H5; eauto
       | eelim H3; eauto
       | eelim (Hssa1 x d1 d2) ; eauto ; intuition ; eauto
      ].
Qed.

Lemma def_def_eq : forall x d1 d2,
  def f x d1 ->
  def f x d2 ->
  d1 = d2.
Proof.
  intros.
  destruct (peq d1 d2) ; auto.
  eelim (unique_def_spec_def x d1 d2) ; eauto.
Qed.

Lemma not_nop_not_jp : forall pc,
  match (fn_code f) ! pc with 
    | None
    | Some (Inop _) 
    | Some (Itailcall _ _ _) 
    | Some (Ireturn _) => True
    | Some (Iop _ _ _ pc') 
    | Some (Iload _ _ _ _ pc')
    | Some (Istore _ _ _ _ pc')
    | Some (Icall _ _ _ _ pc')
    | Some (Ibuiltin _ _ _ pc') => ~ join_point pc' f
    | Some (Icond _ _ pc1 pc2) => ~ join_point pc1 f /\ ~ join_point pc2 f
    | Some (Ijumptable _ succs) => forall s, In s succs -> ~ join_point s f
  end.
Proof.
  intros. flatten; subst; auto; intros; try split; intro Hcont;
     (eapply fn_normalized with (pc:= pc) in Hcont; simpl; go;
      unfold successors_list, successors; 
      rewrite PTree.gmap1; unfold option_map;
      rewrite Eq; go). 
Qed.

Lemma not_nop_not_jp_2 : forall pc,
  match (fn_code f) ! pc with 
    | None
    | Some (Inop _) => True
    | Some (Itailcall _ _ _) 
    | Some (Ireturn _)
    | Some (Iop _ _ _ _) 
    | Some (Iload _ _ _ _ _)
    | Some (Istore _ _ _ _ _)
    | Some (Icall _ _ _ _ _)
    | Some (Ibuiltin _ _ _ _) 
    | Some (Icond _ _ _ _) 
    | Some (Ijumptable _ _) => ~ join_point pc f
  end.
Proof.
  intros. flatten; subst; auto; intros; try split; intro Hcont;
     (eapply fn_phicode_inv in Hcont; auto;
      eapply fn_inop_in_jp in Hcont; auto;
      invh ex; congruence).
Qed.

Lemma njp_not_phidef : forall pc r,
  ~ join_point pc f ->
  assigned_phi_spec (fn_phicode f) pc r -> 
  False.
Proof.
  intros.
  elim H.
  eapply fn_phicode_inv; auto.
  intro Hcont; invh assigned_phi_spec ; go.
Qed.

Lemma def_parcopy_joinpoint : forall pc pc' r,
  assigned_parcopy_spec (fn_parcopycode f) pc r ->
  cfg f pc pc' ->
  ~ join_point pc' f ->
  join_point pc f.
Proof.
  intros. invh assigned_parcopy_spec.
  exploit (parcb_inop f WF pc); eauto. go. intros [s Hpc].
  eapply fn_parcbjp; eauto. 
  invh cfg; allinv. invh In; go. 
Qed.

Lemma jp_not_preceded_by_jp:
  forall pc succ,
  (fn_code f) ! pc = Some (Inop succ) ->
  (fn_phicode f) ! succ <> None ->
  (fn_phicode f) ! pc = None.
Proof.
  intros.
  induction H.
  assert(In pc ((get_preds f) !!! succ)).
  eapply make_predecessors_correct_1; eauto.
  simpl; auto.
  apply fn_normalized_jp
    with (pc := succ) (preds := (get_preds f) !!! succ); auto.
  unfold successors_list in *.
  flatten H; auto. inv H.
Qed.

Lemma wf_cssa_jp_not_jp : forall pc pc',
  join_point pc f ->
  cfg f pc pc' ->
  ~ join_point pc' f.
Proof.
  intros.
  eapply fn_phicode_inv in H; eauto.
  intro Hcont. 
  eapply fn_phicode_inv in Hcont; eauto.
  eapply jp_not_preceded_by_jp in Hcont; eauto.
  
  eapply fn_inop_in_jp in H; eauto. 
  invh ex.
  invh cfg; allinv. invh In; go.
Qed.

Lemma wf_cssa_jp_not_jp_2 : forall pc pc',
  join_point pc' f ->
  cfg f pc pc' ->
  ~ join_point pc f.
Proof.
  intros.
  eapply fn_phicode_inv in H; eauto.
  intro Hcont. 
  eapply fn_phicode_inv in Hcont; eauto.
  eapply jp_not_preceded_by_jp in H; eauto.
  
  eapply fn_inop_in_jp in Hcont; eauto. 
  invh ex.
  invh cfg; allinv. invh In; go.
Qed.

Lemma assigned_parcopy_spec_nop : forall pc r,
  assigned_parcopy_spec (fn_parcopycode f) pc r ->
  exists s, (fn_code f) ! pc = Some (Inop s).
Proof.
  intros.
  invh assigned_parcopy_spec; invh ex.
  exploit parcb_inop; eauto. go.
Qed.

End WF_CSSA.


(* CSSA dom lemma *)
Lemma cssadom_entry : forall f,
  wf_cssa_function f ->
  forall x,
  cssadom f x (fn_entrypoint f) ->
  False.
Proof.
  intros. invh cssadom.
  - invh def;
      inv H2; try congruence;
    contradict NEQ;
    eapply Dom.dom_entry; eauto; intros;
    apply ident_eq. 
  - destruct (fn_entrypoint_inv f) as [[i Hi] Hnj]; auto.
    invh assigned_phi_spec. invh ex.
    elim Hnj. 
    eapply fn_phicode_inv; go. 
  - eelim fn_entrypoint_inv; eauto.
Qed.

Lemma dsd_def_params :forall f x n,
  wf_cssa_function f ->
  reached f n ->
  n <> (fn_entrypoint f) ->
  ext_params f x ->
  cssadom f x n.
Proof.
  intros.
  constructor 1 with (f.(fn_entrypoint)); auto.
  split; auto.
  eapply (@Dom.entry_dom); eauto.
  apply ident_eq.
Qed.

Lemma dsd_pred_njp : forall f,
  wf_cssa_function f -> forall n1 n2 x,
  reached f n1 -> n1 <> f.(fn_entrypoint) ->
  cfg f n1 n2 ->
  cssadom f x n2 ->
  (cssadom f x n1 /\ ~ assigned_phi_spec (fn_phicode f) n2 x) \/
  (def f x n1 /\ ~ assigned_phi_spec (fn_phicode f) n1 x /\ ~ ext_params f x) \/
  (assigned_phi_spec (fn_phicode f) n2 x /\ ~ ext_params f x) \/
  (assigned_parcopy_spec (fn_parcopycode f) n2 x /\ ~ ext_params f x).
Proof.
  intros f H n1 n2 x H0 Hn1 H1 H2. inv H2.
  - assert(Hdom: Dom.dom (cfg f) (exit f) (entry f) def_r n1).
    eapply Dom.sdom_dom_pred ; go. apply ident_eq.
    apply (@Dom.dom_eq_sdom) in Hdom.
    destruct Hdom as [Hdom| Hdom].
    + subst.
      destruct (classic (ext_params f x)) as [E|E].
      * left; split; auto.
        eapply dsd_def_params; eauto.
        eapply ext_params_1; eauto.          
      * { inv H3.
          - right ; left ; repeat split ; auto.
          - right ; left ; split ; auto.
            destruct (fn_cssa f) as [HH HH'] ; auto.
            elim (HH x n1 n1) ; eauto. 
            intuition.
          - left ; split ; eauto.
            econstructor 2 ; eauto.
            destruct (fn_cssa f) as [HH HH'] ; auto.
            elim (HH x n1 n2).
            invh @Dom.sdom.
            intuition.
          - right; left. repeat split; eauto.
            destruct (fn_cssa f) as [HH HH'] ; auto.
            elim (HH x n1 n1).
            intuition.
        }
    + left ; split ; auto.
      econstructor 1 ; eauto.
      intro Hcont. inv Hcont.
      exploit (def_def_eq f H x n2 def_r); eauto.
      intros. subst. inv H4. intuition.
    + apply ident_eq.
  - right ; right ; left; split; auto.
    intro. inv H2.
    + eelim fn_cssa_params; eauto.
      intuition. go.
    + intuition. go. 
  - right; right; right; split; auto.
    intro. inv H2.
    + eelim fn_cssa_params; eauto.
      intuition. go.
    + intuition. go. 
Qed.

Ltac normalized := 
  try match goal with 
    | id : assigned_phi_spec (fn_phicode _) ?PC _ |- _ =>
      solve [ eelim njp_not_phidef with (pc:= PC); go
            | eelim njp_not_phidef ; go ]
    | id: (fn_code _) ! ?PC = _ |- _ => 
      solve [eelim fn_entry_pred with (pc:= PC); go]
    | id: (fn_parcopycode _) ! (fn_entrypoint _) = Some _ |- _ =>
      solve [erewrite fn_no_parcb_at_entry in id ; eauto; congruence]
    | _ => 
      solve [exploit fn_entry; eauto ; intros; invh ex ; congruence
            | invh assigned_code_spec; try congruence
            | eapply def_parcopy_joinpoint; eauto; go
            | exploit assigned_parcopy_spec_nop; eauto; intros ; invh ex ; congruence
            | eapply wf_cssa_jp_not_jp; go
            | eapply wf_cssa_jp_not_jp_2; go
            ]
      end.

Ltac ssa := 
  try match goal with 
          | id: (fn_parcopycode _) ! ?PC = Some ?PCB |- (NoDup (map parc_dst ?PCB)) =>
            solve [eapply wf_cssa_nodup_parcb; eauto]
          | _ =>
            solve [ eapply wf_cssa_def_parcopy_code; eauto; go
                  | eapply wf_cssa_def_code_parcopy; eauto; go
                  | eapply wf_cssa_def_phi_code; eauto; go
                  | eelim wf_cssa_def_phi_parcopy; eauto; go]
      end.

Lemma dsd_pred_not_join_point : forall f, 
  wf_cssa_function f -> forall n1 n2 x,
  reached f n1 -> 
  cfg f n1 n2 ->
  cssadom f x n2 ->
  ~ join_point n2 f -> 
  (ext_params f x /\ n1 = fn_entrypoint f) \/
  (cssadom f x n1 /\ ~ assigned_code_spec (fn_code f) n1 x) \/
  (assigned_code_spec (fn_code f) n1 x 
   /\ ~ assigned_phi_spec (fn_phicode f) n1 x
   /\ ~ assigned_parcopy_spec (fn_parcopycode f) n1 x).
Proof.
  intros.
  invh cssadom; try congruence; normalized. 
  assert(Hd: Dom.dom (cfg f) (exit f) (entry f) def_r n1).
  { eapply sdom_dom_pred; eauto. apply ident_eq. }
  destruct (classic (assigned_phi_spec (fn_phicode f) n1 x)).
  - right; left; split.
    + econstructor 2; eauto.
    + ssa. 
  - destruct (peq def_r n1).
    + subst.
      { invh def; auto.
        - right; right; repeat split; auto; ssa.
        - right ; left ; split; auto.
          econstructor 2 ; eauto.
        - right; left ; split; auto.
          * econstructor 3; eauto.
            normalized. 
          * ssa. 
      } 
    + right ; left ; split; auto.
      * econstructor 1; eauto; go.
      * intro. eelim n; eapply def_def_eq ; eauto; go.
Qed.

(* Other utility lemma *)
Fixpoint In_dst_parcb (r : reg) (parcb : parcopyblock) : bool :=
  match parcb with
  | nil => false
  | Iparcopy src dst :: q =>
      if peq dst r
      then true
      else In_dst_parcb r q
  end.

Lemma In_dst_parcb_true :
  forall r parcb,
  In_dst_parcb r parcb = true ->
  exists src, In (Iparcopy src r) parcb.
Proof.
  induction parcb; go.
  intros.
  simpl in *.
  flatten H.
  exists r0. left. congruence.
  exploit IHparcb; auto.
  intros.
  destruct H0 as [src Hin].
  exists src; auto.
Qed.

Lemma In_dst_parcb_false :
  forall r parcb,
  In_dst_parcb r parcb = false ->
  forall src, ~ In (Iparcopy src r) parcb.
Proof.
  induction parcb; go.
  intros.
  simpl in *.
  flatten H.
  unfold not; intros.
  destruct H0; go.
  exploit IHparcb; go.
Qed.

Fixpoint In_dst_phib (r : reg) (phib : phiblock) : bool :=
  match phib with
  | nil => false
  | Iphi args dst :: q =>
      if peq dst r
      then true
      else In_dst_phib r q
  end.

Lemma In_dst_phib_true :
  forall r phib,
  In_dst_phib r phib = true ->
  exists args, In (Iphi args r) phib.
Proof.
  induction phib; go.
  intros.
  simpl in *.
  flatten H.
  exists l. left. congruence.
  exploit IHphib; auto.
  intros.
  destruct H0 as [args Hin].
  exists args; auto.
Qed.

Lemma In_dst_phib_false :
  forall r phib,
  In_dst_phib r phib = false ->
  forall args, ~ In (Iphi args r) phib.
Proof.
  induction phib; go.
  intros.
  simpl in *.
  flatten H.
  unfold not; intros.
  destruct H0; go.
  exploit IHphib; go.
Qed.

Fixpoint In_reg r l :=
  match l with
  | nil => false
  | h :: t => if peq r h then true else In_reg r t
  end.

Lemma In_reg_correct_true :
  forall r l,
  In_reg r l = true ->
  In r l.
Proof.
  induction l; intros.
  go. simpl in *. flatten H; go.
Qed.

Lemma phi_store_other :
  forall k rs r phib,
  (forall args dst, In (Iphi args dst) phib ->
    r <> dst) ->
  rs !! r = (phi_store k phib rs) !! r.
Proof.
  intros k rs r phib.
  induction phib; go.
  intros. simpl. destruct a.
  destruct (nth_error l k); go.
  rewrite PMap.gso; go.
Qed.

Definition phi_dst phiinstr :=
  match phiinstr with
  | Iphi args dst => dst
  end.

Lemma phi_dst_in :
  forall phib r args,
  In (Iphi args r) phib ->
  In r (map phi_dst phib).
Proof.
  induction phib; intros.
  inv H.
  simpl in *.
  destruct H.
  + destruct a; simpl in *.
    left; congruence.
  + right; go.
Qed.

Lemma phi_dst_exists_src :
  forall phib r,
  In r (map phi_dst phib) ->
  exists args, In (Iphi args r) phib.
Proof.
  induction phib; go; intros.
  simpl in *.
  destruct a. destruct H.
  + simpl in H. rewrite H in *.
    exists l; auto.
  + exploit (IHphib r); eauto; intros.
    destruct H0 as [args H0].
    go.
Qed.

Lemma no_dups_in_dst_phib_aux :
  forall phib,
  (forall r args args',
    In (Iphi args r) phib ->
    In (Iphi args' r) phib ->
    args = args') ->
  NoDup phib ->
  NoDup (map phi_dst phib).
Proof.
  induction phib; intros; go.
  simpl.
  constructor; unfold not; intros.
  destruct a.
  simpl in H1.
  exploit phi_dst_exists_src; eauto; intros.
  destruct H2 as [args Hin].
  exploit (H r l args); auto; intros Heq.
  rewrite Heq in *.
  inv H0; auto.
  apply IHphib; intros.
  exploit (H r args args'); auto.
  inv H0; congruence.
Qed.

Lemma no_dups_in_dst_phib :
  forall phib f pc,
  wf_cssa_function f ->
  (fn_phicode f) ! pc = Some phib ->
  NoDup (map phi_dst phib).
Proof.
  intros.
  induction H.
  induction fn_cssa.
  destruct H0 as [Hphi Hparc].
  exploit (Hphi pc phib); auto.
  intros Hphib.
  destruct Hphib.
  apply no_dups_in_dst_phib_aux; auto.
Qed.

Lemma phi_store_in_aux :
  forall phib args r k arg rs,
  NoDup (map phi_dst phib) ->
  In (Iphi args r) phib ->
  nth_error args k = Some arg ->
  (phi_store k phib rs) !! r = rs !! arg.
Proof.
  induction phib; intros.
  inv H0.
  simpl in *. flatten; destruct H0; go.
  assert(EQ1: r0 = r) by congruence. rewrite EQ1 in *.
  assert(EQ2: l = args) by congruence. rewrite EQ2 in *.
  rewrite PMap.gss; auto. congruence.
  simpl in H. inv H.
  assert(Hin: In r (map phi_dst phib)).
  eapply phi_dst_in; eauto.
  assert(r <> r0) by congruence.
  rewrite PMap.gso; auto.
  go.
  inv H; go.
Qed.

Lemma phi_store_in :
  forall phib f pc r args k arg rs,
  wf_cssa_function f ->
  (fn_phicode f) ! pc = Some phib ->
  In (Iphi args r) phib ->
  nth_error args k = Some arg ->
  (phi_store k phib rs) !! r = rs !! arg.
Proof.
  intros.
  assert(HNoDup: NoDup (map phi_dst phib)).
  eapply no_dups_in_dst_phib; eauto.
  eapply phi_store_in_aux; eauto.
Qed.


Lemma fn_phiargs: forall f, 
  wf_cssa_function f -> 
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

(** ** The [is_edge] predicate *)
Variant is_edge (code : code) : node -> node -> Prop :=
    Edge : forall (i : positive) (j : node) (instr : instruction),
           code ! i = Some instr ->
           In j (successors_instr instr) -> is_edge code i j.

Lemma pred_is_edge_help: forall code i j k,
  index_pred  (make_predecessors code successors_instr) i j = Some k -> 
  (is_edge code i j).
Proof.
  intros. 
  unfold index_pred in *. 
  exploit get_index_some_in ; eauto ; intros.
  exploit (make_predecessors_some code successors_instr j); eauto.
  unfold make_preds, successors_list in *.
  flatten Eq. inv H0.
  intros (ins & Hins).
  assert (HH:= make_predecessors_correct2 code successors_instr i ins j Hins H0); auto. 
  eapply Edge; eauto. 
Qed.
  
Lemma pred_is_edge: forall code i j k,
                      index_pred (make_predecessors code successors_instr) i j = Some k -> is_edge code i j.
Proof.
  intros. 
  exploit_dstr pred_is_edge_help; eauto.
Qed.

Lemma is_edge_succs_not_nil: forall tf i j, 
  is_edge (fn_code tf) i j ->
  exists succtfi, (successors tf)!i = Some succtfi.
Proof.
  intros. inv H.
  unfold successors. rewrite PTree.gmap1. rewrite H0. 
  simpl; eauto.
Qed.

Lemma is_edge_insuccs: forall tf i j, 
  is_edge (fn_code tf) i j -> 
  (exists succtfi, (successors tf) ! i = Some succtfi /\ In j succtfi).
Proof.
  intros. 
  destruct (is_edge_succs_not_nil _ _ _ H) as [succtfi Hsuccs].
  exists succtfi ; intuition.
  inv H.
  unfold successors in *. 
  rewrite PTree.gmap1 in Hsuccs. rewrite H0 in Hsuccs. 
  inv Hsuccs; auto.
Qed.

(* Misc lemmas *)

Lemma in_parcb_dst_exists_src (r : reg)
    (parcb : parcopyblock) :
  In r (map parc_dst parcb) ->
  exists src, In (Iparcopy src r) parcb.
Proof.
  induction parcb; intros.
  { simpl in H. contradiction. }
  simpl.
  destruct a.
  case_eq (peq r r1); intros.
  + rewrite e in *.
    exists r0. auto.
  + simpl in H.
    destruct H. congruence.
    assert (IN_parcb: exists src :
      reg, In (Iparcopy src r) parcb).
    auto. destruct IN_parcb as [src IN_parcb].
    eauto.
Qed.

Lemma parc_dst_in :
  forall parcb src r,
  In (Iparcopy src r) parcb ->
  In r (map parc_dst parcb).
Proof.
  induction parcb; go; intros.
  simpl in *.
  destruct H; go.
Qed.

Global Hint Resolve parc_dst_in: core.

(* Stores *)

Lemma parcb_other :
  forall parcb r rs,
  (forall src dst,
    In (Iparcopy src dst) parcb ->
    r <> dst) ->
  (parcopy_store parcb rs) # r = rs # r.
Proof.
  induction parcb; auto; intros.
  simpl in *.
  flatten.
  case_eq (peq r r1); intros.
  + rewrite e in *.
    assert (r1 <> r1) by eauto.
    congruence.
  + rewrite PMap.gso; eauto.
Qed.

Lemma parcb_store_in :
  forall parcb rs r src,
  In (Iparcopy src r) parcb ->
  NoDup (map parc_dst parcb) ->
  (parcopy_store parcb rs) # r = rs # src.
Proof.
  induction parcb; intros.
  + inv H.
  + simpl in *.
    destruct a.
    destruct H.
    - assert (EQ: r1 = r) by congruence.
      rewrite EQ.
      rewrite PMap.gss.
      congruence.
    - inv H0.
      assert (In r (map parc_dst parcb)) by
        (eapply parc_dst_in; eauto).
      assert (r <> r1) by congruence.
      rewrite PMap.gso; auto.
Qed.

(* Lists *)
Lemma nodups_rev :
  forall (l : list positive),
  NoDup (rev l) ->
  NoDup l.
Proof.
  induction l; intros.
  + auto.
  + simpl in *.
    constructor.
    assert(~ In a (rev l ++ nil)).
    apply NoDup_remove_2. auto.
    rewrite app_nil_r in H0.
    unfold not; intros.
    apply H0.
    rewrite <- in_rev; auto.
    assert (NoDup (rev l ++ nil)).
    apply NoDup_remove_1 with a. auto.
    rewrite app_nil_r in H0.
    auto.
Qed.

Lemma list_norepet_NoDup :
  forall (l : list node),
  list_norepet l ->
  NoDup l.
Proof.
  intros.
  induction H; go.
Qed.

Lemma In_Infst :
  forall l (pc : node) (ins : instruction),
  In (pc, ins) l ->
  In pc (map fst l).
Proof.
  induction l; auto; intros.
  simpl.
  destruct a; simpl in *.
  destruct H; auto.
  + left; congruence.
  + right; eauto.
Qed.

Lemma In_Infst_parcb :
  forall l (pc : node) (parcb : parcopyblock),
  In (pc, parcb) l ->
  In pc (map fst l).
Proof.
  induction l; auto; intros.
  simpl.
  destruct a; simpl in *.
  destruct H; auto.
  + left; congruence.
  + right; eauto.
Qed.

Lemma In_Infst_phib :
  forall l (pc : node) (phib : phiblock),
  In (pc, phib) l ->
  In pc (map fst l).
Proof.
  induction l; auto; intros.
  simpl.
  destruct a; simpl in *.
  destruct H; auto.
  + left; congruence.
  + right; eauto.
Qed.

Lemma In_Insnd_phib :
  forall l (pc : node) (phib : phiblock),
  In (pc, phib) l ->
  In phib (map snd l).
Proof.
  induction l; auto; intros.
  simpl.
  destruct a; simpl in *.
  destruct H; auto.
  + left; congruence.
  + right; eauto.
Qed.

Lemma In_Insnd :
  forall elts (r : reg) (l : list reg),
  In (r, l) elts ->
  In l (map snd elts).
Proof.
  induction elts; auto; intros.
  simpl.
  destruct a; simpl in *.
  destruct H; auto.
  + left; congruence.
  + right; eauto.
Qed.

(* use and def *)

Require Import Classical.

Lemma exists_def : forall f r u,
   use f r u ->                
   exists d, def f r d.
Proof.
  intros.
  destruct (classic (ext_params f r)).
  - exists (fn_entrypoint f) ; go.
  - destruct (classic (exists pc, assigned_code_spec (fn_code f) pc r)).
    + invh ex ; go.
    + destruct (classic (exists pc, assigned_phi_spec (fn_phicode f) pc r)).
      invh ex ; go.
      destruct (classic (exists pc, assigned_parcopy_spec (fn_parcopycode f) pc r)).
      * invh ex; go. 
      * eelim H0 ; go. 
Qed.      

(* decision procedure for "used" *)
Notation reg_use := SSARegSet.add.

Fixpoint reg_list_use (rl: list reg) (ruse: SSARegSet.t) : SSARegSet.t :=
  match rl with
  | nil => ruse
  | r1 :: rest => reg_list_use rest (reg_use r1 ruse)
  end.

Definition search_instruction ruse ins :=
  match ins with
  | Inop s => ruse
  | Iop op args res s => reg_list_use args ruse
  | Iload chunk addr args dst s => reg_list_use args ruse
  | Istore chunk addr args src s => reg_list_use (src :: args) ruse
  | Icall sig (inl r) args res s => reg_list_use (r :: args) ruse
  | Icall sig os args res s => reg_list_use args ruse
  | Itailcall sig (inl r) args => reg_list_use (r :: args) ruse
  | Itailcall sig os args => reg_list_use args ruse
  | Ibuiltin ef args res s => reg_list_use (params_of_builtin_args args) ruse 
  | Icond cond args ifso ifnot => reg_list_use args ruse
  | Ijumptable arg tbl => reg_use arg ruse
  | Ireturn None => ruse
  | Ireturn (Some arg) => reg_use arg ruse
  end.

Definition search_parcb ruse (parcb : parcopyblock) :=
  fold_left
    (fun acc parc =>
      match parc with
      | Iparcopy src dst =>
          reg_use src acc
      end)
    parcb ruse.

Definition search_phib ruse (phib : phiblock) :=
  fold_left
    (fun acc phi =>
      match phi with
      | Iphi args dst =>
          reg_list_use args acc
      end)
    phib ruse.

Definition search_code ruse (code : code) :=
  fold_left
    (fun acc pcins => search_instruction acc (snd pcins))
    (PTree.elements code)
    ruse.

Definition search_parcopycode ruse (parcode : parcopycode) :=
  fold_left
    (fun acc pcins => search_parcb acc (snd pcins))
    (PTree.elements parcode)
    ruse.

Definition search_phicode ruse (phicode : phicode) :=
  fold_left
    (fun acc pcins => search_phib acc (snd pcins))
    (PTree.elements phicode)
    ruse.

Definition search_used (f : function) :=
  (search_code
    (search_parcopycode
      (search_phicode SSARegSet.empty (fn_phicode f))
      (fn_parcopycode f))
    (fn_code f)).

Lemma reg_list_use_correct_1 :
  forall rl r ruse,
  SSARegSet.In r ruse ->
  SSARegSet.In r (reg_list_use rl ruse).
Proof.
  induction rl; intros; simpl in *; auto.
  unfold reg_use.
  apply IHrl.
  rewrite SSARegSet.MSet.add_spec; go.
Qed.

Lemma reg_list_use_correct_2 :
  forall rl r ruse,
  In r rl ->
  SSARegSet.In r (reg_list_use rl ruse).
Proof.
  induction rl; intros.
  contradiction.
  simpl in *.
  destruct H.
  + rewrite H in *.
    apply reg_list_use_correct_1.
    unfold reg_use.
    apply SSARegSet.MSet.add_spec; go.
  + apply IHrl; auto.
Qed.

Lemma search_instruction_correct_1 :
  forall f r pc ins ruse,
  (fn_code f) ! pc = Some ins ->
  use_code f r pc ->
  SSARegSet.In r (search_instruction ruse ins).
Proof.
  intros.
  unfold search_instruction.
  destruct ins.
  + inv H0; go.
  + inv H0; go.
    replace args with l in *; go.
    apply reg_list_use_correct_2; auto.
  + inv H0; go.
    replace args with l in *; go.
    apply reg_list_use_correct_2; auto.
  + inv H0; go.
    replace args with l in *; go.
    allinv. 
    apply reg_list_use_correct_2; auto.
  + flatten; allinv.
    inv H0; allinv; go.
    apply reg_list_use_correct_2; auto.
    inv H0; allinv; go.
    apply reg_list_use_correct_2; auto.
  + flatten.
    inv H0; allinv; go.
    apply reg_list_use_correct_2; auto.
    inv H0; allinv; go.
    apply reg_list_use_correct_2; auto.
  + inv H0; allinv; go.
    apply reg_list_use_correct_2; auto.
  + inv H0; allinv; go.
    apply reg_list_use_correct_2; auto.
  + inv H0; allinv; go.
    rewrite SSARegSet.MSet.add_spec; go.
  + flatten.
    inv H0; allinv; go.
    rewrite SSARegSet.MSet.add_spec; go.
    inv H0; go.
Qed.

Lemma search_instruction_correct_2 :
  forall r ins ruse,
  SSARegSet.In r ruse ->
  SSARegSet.In r (search_instruction ruse ins).
Proof.
  intros.
  destruct ins; go;
  unfold search_instruction; flatten;
  try (apply reg_list_use_correct_1; auto);
  rewrite SSARegSet.MSet.add_spec; go.
Qed.

Lemma search_code_correct_aux :
  forall (elems : list (node * instruction)) f r ruse pc ins,
  In (pc, ins) elems ->
  (fn_code f) ! pc = Some ins ->
  use_code f r pc ->
  SSARegSet.In r
    (fold_right
      (fun pcins acc =>
        search_instruction acc (snd pcins))
      ruse elems).
Proof.
  induction elems; intros.
  inv H.
  simpl in *.
  destruct H.
  + rewrite H in *; simpl in *.
    eapply search_instruction_correct_1; eauto.
  + apply search_instruction_correct_2.
    eapply IHelems; eauto.
Qed.

Lemma search_code_correct_1 :
  forall f r pc ruse,
  use_code f r pc ->
  SSARegSet.In r (search_code ruse (fn_code f)).
Proof.
  intros.
  unfold search_code.
  rewrite <- fold_left_rev_right.
  inv H;
  eapply search_code_correct_aux; eauto;
  try (rewrite <- in_rev; apply PTree.elements_correct; auto);
  go.
Qed.

Lemma search_code_correct_aux2 :
  forall (elems : list (node * instruction)) r ruse,
  SSARegSet.In r ruse ->
  SSARegSet.In r
    (fold_right
      (fun pcins acc =>
        search_instruction acc (snd pcins))
      ruse elems).
Proof.
  induction elems; intros; simpl; auto.
  eapply search_instruction_correct_2; eauto.
Qed.

Lemma search_code_correct_2 :
  forall f r ruse,
  SSARegSet.In r ruse ->
  SSARegSet.In r (search_code ruse (fn_code f)).
Proof.
  intros.
  unfold search_code.
  rewrite <- fold_left_rev_right.
  eapply search_code_correct_aux2; eauto.
Qed.

Lemma search_parcb_correct_aux1 :
  forall r parcb ruse dst,
  In (Iparcopy r dst) parcb ->
  SSARegSet.In r
    (fold_right
      (fun parc acc =>
        match parc with
        | Iparcopy src _ => reg_use src acc
        end) ruse parcb).
Proof.
  induction parcb; simpl; auto; intros.
  contradiction.
  destruct H.
  + rewrite H.
    apply SSARegSet.MSet.add_spec; go.
  + simpl. flatten.
    apply SSARegSet.MSet.add_spec; go.
    right.
    eapply IHparcb; eauto.
Qed.

Lemma search_parcb_correct_aux2 :
  forall r parcb ruse,
  SSARegSet.In r ruse ->
  SSARegSet.In r
    (fold_right
      (fun parc acc =>
        match parc with
        | Iparcopy src _ => reg_use src acc
        end) ruse parcb).
Proof.
  induction parcb; simpl; auto; intros.
  flatten.
  apply SSARegSet.MSet.add_spec; go.
  right.
  apply IHparcb; auto.
Qed.

Lemma search_parcb_correct_1 :
  forall f r pc parcb ruse,
  (fn_parcopycode f) ! pc = Some parcb ->
  use_parcopycode f r pc ->
  SSARegSet.In r (search_parcb ruse parcb).
Proof.
  intros.
  unfold search_parcb.
  rewrite <- fold_left_rev_right.
  inv H0.
  replace parcb0 with parcb in *; go.
  eapply search_parcb_correct_aux1 with (dst := dst); eauto.
  rewrite <- in_rev; auto.
Qed.

Lemma search_parcb_correct_2 :
  forall r parcb ruse,
  SSARegSet.In r ruse ->
  SSARegSet.In r (search_parcb ruse parcb).
Proof.
  intros.
  unfold search_parcb.
  rewrite <- fold_left_rev_right.
  eapply search_parcb_correct_aux2; eauto.
Qed.

Lemma search_parcopycode_correct_aux1 :
  forall (elems : list (node * parcopyblock)) f r
    ruse pc parcb,
  In (pc, parcb) elems -> 
  (fn_parcopycode f) ! pc = Some parcb ->
  use_parcopycode f r pc ->
  SSARegSet.In r
    (fold_right
      (fun pcins acc =>
        search_parcb acc (snd pcins))
      ruse elems).
Proof.
  induction elems; simpl; intros; auto.
  contradiction.
  destruct H.
  + rewrite H; simpl.
    eapply search_parcb_correct_1; eauto.
  + eapply search_parcb_correct_2; eauto.
Qed.

Lemma search_parcopycode_correct_1 :
  forall f r pc ruse,
  use_parcopycode f r pc ->
  SSARegSet.In r (search_parcopycode ruse (fn_parcopycode f)).
Proof.
  intros.
  unfold search_parcopycode.
  rewrite <- fold_left_rev_right.
  inv H.
  eapply search_parcopycode_correct_aux1; eauto.
  rewrite <- in_rev. apply PTree.elements_correct; auto.
  go.
Qed.

Lemma search_parcopycode_correct_aux2 :
  forall (elems : list (node * parcopyblock)) r ruse,
  SSARegSet.In r ruse ->
  SSARegSet.In r
    (fold_right
      (fun pcins acc =>
        search_parcb acc (snd pcins))
      ruse elems).
Proof.
  induction elems; intros; simpl; auto.
  eapply search_parcb_correct_2; eauto.
Qed.

Lemma search_parcopycode_correct_2 :
  forall f r ruse,
  SSARegSet.In r ruse ->
  SSARegSet.In r (search_parcopycode ruse (fn_parcopycode f)).
Proof.
  intros.
  unfold search_parcopycode.
  rewrite <- fold_left_rev_right.
  apply search_parcopycode_correct_aux2; auto.
Qed.

Lemma search_phib_correct_aux1 :
  forall r phib args ruse dst,
  In (Iphi args dst) phib ->
  In r args ->
  SSARegSet.In r
    (fold_right
      (fun phi acc =>
        match phi with
        | Iphi args _ => reg_list_use args acc
        end) ruse phib).
Proof.
  induction phib; simpl; auto; intros.
  contradiction.
  destruct H.
  + rewrite H.
    eapply reg_list_use_correct_2; go.
  + simpl. flatten.
    eapply reg_list_use_correct_1; go.
Qed.

Lemma search_phib_correct_aux2 :
  forall r phib ruse,
  SSARegSet.In r ruse ->
  SSARegSet.In r
    (fold_right
      (fun phi acc =>
        match phi with
        | Iphi args _ => reg_list_use args acc
        end) ruse phib).
Proof.
  induction phib; simpl; auto; intros.
  flatten.
  eapply reg_list_use_correct_1; go.
Qed.

Lemma search_phib_correct_1 :
  forall f r pc pred phib ruse,
  wf_cssa_function f ->
  (fn_phicode f) ! pc = Some phib ->
  use_phicode f r pred ->
  cfg f pred pc ->
  SSARegSet.In r (search_phib ruse phib).
Proof.
  intros.
  unfold search_phib.
  rewrite <- fold_left_rev_right.
  inv H1.
  assert(EQ: pc0 = pc).
  {
    assert(Hjp: join_point pc f).
    apply fn_phicode_inv; auto. congruence.
    assert(In pc (successors f) !!! pred).
    invh cfg.
    unfold successors.
    unfold successors_list.
    rewrite PTree.gmap1. unfold option_map.
    flatten; flatten Eq; auto.
    exploit (fn_normalized f); eauto; intros Hinop.
    exploit pred_is_edge_help; eauto; intros Hedge.
    inv Hedge.
    rewrite Hinop in H3.
    assert(Hinstr: instr = Inop pc) by congruence.
    rewrite Hinstr in *.
    simpl in *.
    destruct H4; auto. contradiction.
  }
  rewrite EQ in *.
  assert(EQphib: phib0 = phib) by congruence.
  rewrite EQphib in *.
  apply search_phib_correct_aux1
    with (args := args) (dst := dst).
  rewrite <- in_rev. auto.
  eapply nth_error_in; eauto.
Qed.

Lemma search_phib_correct_2 :
  forall r phib ruse,
  SSARegSet.In r ruse ->
  SSARegSet.In r (search_phib ruse phib).
Proof.
  intros.
  unfold search_phib.
  rewrite <- fold_left_rev_right.
  eapply search_phib_correct_aux2; eauto.
Qed.

Lemma search_phicode_correct_aux1 :
  forall (elems : list (node * phiblock)) f r
    ruse pc pred phib,
  wf_cssa_function f ->
  In (pc, phib) elems -> 
  (fn_phicode f) ! pc = Some phib ->
  use_phicode f r pred ->
  cfg f pred pc ->
  SSARegSet.In r
    (fold_right
      (fun pcphib acc =>
        search_phib acc (snd pcphib))
      ruse elems).
Proof.
  induction elems; simpl; intros; auto.
  contradiction.
  destruct H0.
  + rewrite H0; simpl.
    eapply search_phib_correct_1; eauto.
  + eapply search_phib_correct_2; eauto.
Qed.

Lemma search_phicode_correct_1 :
  forall f r pc ruse,
  wf_cssa_function f ->
  use_phicode f r pc ->
  SSARegSet.In r (search_phicode ruse (fn_phicode f)).
Proof.
  intros.
  unfold search_phicode.
  rewrite <- fold_left_rev_right.
  inv H0.
  eapply search_phicode_correct_aux1; eauto.
  rewrite <- in_rev. apply PTree.elements_correct; auto.
  go.
  exploit pred_is_edge_help; eauto; intros.
  inv H0. go.
Qed.

Lemma search_used_correct :
  forall f pc r,
  wf_cssa_function f ->
  use f r pc ->
  SSARegSet.In r (search_used f).
Proof.
  intros f pc r WF H.
  inv H;
  unfold search_used.
  + eapply search_code_correct_1; eauto.
  + eapply search_code_correct_2; eauto.
    eapply search_parcopycode_correct_2; eauto.
    eapply search_phicode_correct_1; eauto.
  + eapply search_code_correct_2; eauto.
    eapply search_parcopycode_correct_1; eauto.
Qed.

Definition param_set (f:function) : SSARegSet.t :=
  List.fold_right SSARegSet.add SSARegSet.empty (fn_params f).  

Lemma nodup_in_parcb_dst_aux:
  forall parcb,
  NoDup parcb ->
  (forall dst src src',
    In (Iparcopy src dst) parcb ->
    In (Iparcopy src' dst) parcb ->
    src = src') ->
  NoDup (map parc_dst parcb).
Proof.
  induction parcb; intros.
  + go.
  + simpl. constructor.
    unfold not; intros.
    inv H. destruct a. simpl in *.
    exploit in_parcb_dst_exists_src; eauto; intros.
    destruct H.
    assert(x = r); go. 
    apply IHparcb; inv H; go.
Qed.

Lemma nodup_in_parcb_dst :
  forall f pc parcb,
  wf_cssa_function f ->
  (fn_parcopycode f) ! pc = Some parcb ->
  NoDup (map parc_dst parcb).
Proof.
  intros f pc parcb WF Hparcb.
  induction WF.
  induction fn_cssa.
  destruct H0.
  exploit H1; eauto; intros.
  apply nodup_in_parcb_dst_aux; go.
  specialize (H1 pc parcb).
  tauto. intuition eauto.
Qed.

