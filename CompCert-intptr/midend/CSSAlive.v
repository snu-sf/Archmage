
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Lattice.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import Op.
Require Import Registers.
Require Import SSA.
Require Import SSAutils.
Require Import CSSA.
Require Import Kildall.
Require Import DLib.
Require Import CSSAutils.
Require Import Classical.

(** * Liveness analysis over CSSApar *)

Notation reg_live := SSARegSet.add.
Notation reg_dead := SSARegSet.remove.

Definition reg_option_live (or: option reg) (lv: SSARegSet.t) :=
  match or with
  | None => lv
  | Some r => reg_live r lv
  end.

Definition reg_sum_live (ros: reg + ident) (lv: SSARegSet.t) :=
  match ros with
  | inl r => reg_live r lv
  | inr s => lv
  end.

Fixpoint reg_list_live (rl: list reg) (lv: SSARegSet.t) {struct rl} : SSARegSet.t :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_live rs (reg_live r1 lv)
  end.

Fixpoint reg_list_dead (rl: list reg) (lv: SSARegSet.t) {struct rl} : SSARegSet.t :=
  match rl with
  | nil => lv
  | r1 :: rs => reg_list_dead rs (reg_dead r1 lv)
  end.

Definition transfer_instruction (i : instruction)
    (after: SSARegSet.t) :=
  match i with
  | Inop s =>
      after
  | Iop op args res s =>  
      reg_list_live args (reg_dead res after)        
  | Iload chunk addr args dst s => 
      reg_list_live args (reg_dead dst after)
  | Istore chunk addr args src s =>
      reg_list_live args (reg_live src after)
  | Icall sig ros args res s =>
      reg_list_live args
       (reg_sum_live ros (reg_dead res after))
  | Itailcall sig ros args =>
      reg_list_live args
        (reg_sum_live ros SSARegSet.empty)
  | Ibuiltin ef args (BR res) s =>
      reg_list_live (params_of_builtin_args args) (reg_dead res after)
  | Ibuiltin ef args res s =>
      reg_list_live (params_of_builtin_args args) after
  | Icond cond args ifso ifnot =>
      reg_list_live args after
  | Ijumptable arg tbl =>
      reg_live arg after
  | Ireturn optarg =>
      reg_option_live optarg SSARegSet.empty
  end.

Definition transfer_parcb (parcb : parcopyblock)
  (after: SSARegSet.t) :=
    reg_list_live
      (map parc_src parcb)
      after.

Definition transfer_parcb' (parcb' : parcopyblock)
  (after: SSARegSet.t) :=
    reg_list_dead
      (map parc_dst parcb')
      after.

Definition transfer
    (f: CSSA.function) (pc: node)
    (after: SSARegSet.t) : SSARegSet.t :=
  match f.(fn_code)!pc with
  | None =>
      SSARegSet.empty
  | Some i =>
      match (fn_phicode f) ! pc with
      | None => 
          match (fn_parcopycode f) ! pc with
          | None => transfer_instruction i after
          | Some parcb => transfer_parcb parcb after
          end
      | Some phib =>
          match (fn_parcopycode f) ! pc with
          | None =>
              (* should not happen *)
              transfer_instruction i after
          | Some parcb' =>
              transfer_parcb' parcb'
                (transfer_instruction i after)
          end
      end
  end.

(** The liveness analysis is then obtained by instantiating the
  general framework for backward dataflow analysis provided by
  module [Kildall].  *)

Module RegsetLat := LFSet(SSARegSet).
Module DS := Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward).

Definition analyze (f: function): option (PMap.t SSARegSet.t) :=
  DS.fixpoint f.(fn_code) successors_instr (transfer f).

Section WF_LIVE.

Variable f : CSSA.function.

Definition Lout (live : PMap.t SSARegSet.t) :=
  fun pc => live # pc.

Definition wf_live (live : positive -> SSARegSet.t) :=
  forall r pc,
  cssaliveout_spec f r pc ->
  SSARegSet.In r (live pc).

Lemma reg_list_live_incl : forall x l s, 
    SSARegSet.In x s ->
    SSARegSet.In x (reg_list_live l s).
Proof.
  induction l ; intros ; simpl ; auto.
  eapply IHl ; eauto.
  eapply SSARegSet.add_2 ; eauto.
Qed.
  
Lemma reg_list_live_incl_2 : forall x l s, 
    In x l ->
    SSARegSet.In x (reg_list_live l s).
Proof.
  induction l ; intros ; inv H.
  simpl. 
  eapply reg_list_live_incl ; eauto.
  eapply SSARegSet.add_1 ; eauto.
  eapply IHl ; eauto.
Qed.

Lemma reg_list_dead_not_in : forall l r s,
  SSARegSet.In r s ->
  ~ In r l ->
  SSARegSet.In r (reg_list_dead l s).
Proof.
  induction l ; intros; go.
  simpl.
  eapply IHl; eauto.
  eapply SSARegSet.remove_2 ; eauto.
  intro Hcont ; subst ; go.
Qed.

Lemma live_wf_live :
  wf_cssa_function f ->
  forall lv, analyze f = Some lv ->
  wf_live (Lout lv).
Proof.
  intros.
  unfold wf_live; intros.
  unfold analyze in *.
  induction H1.
  - invh cfg.
    exploit DS.fixpoint_solution ; eauto.
    + unfold transfer, transfer_parcb', transfer_parcb.
      intros. rewrite H1. go.
    + unfold transfer, transfer_parcb', transfer_parcb.
      invh use.
      * invh use_code ; rewrite H3; 
          flatten; simpl; flatten;
            try solve [eapply reg_list_live_incl_2; eauto];
            try solve [eelim wf_cssa_norm_1 ; eauto; go];
            try solve [eelim (parcb_inop f H pc') ; eauto; go];
            try solve [invh In ; eauto using reg_list_live_incl_2,
                                 reg_list_live_incl, SSARegSet.add_1];
            try solve [eauto using SSARegSet.add_1].        
            
      * assert (Hins: exists i, (fn_code f) ! pc' = Some i) 
        by (eapply fn_code_closed; eauto). 
        destruct Hins as [ins' Hins']. rewrite Hins'.
        { flatten ; simpl.
          - (* WF_CSSA : no two successive joinpoints (pc' + succ) *)
            invh use_phicode.
            assert ( (fn_phicode f) ! pc' = None ). 
            { eapply index_pred_some_nth in KPRED.
              unfold successors_list in KPRED.
              flatten KPRED.
              - eapply fn_normalized_jp with (pc:= pc0) (preds:= l) ; go.
                eapply nth_error_in; eauto. 
              - eapply nth_error_in in KPRED; go. 
            }          
        congruence. 
          - exploit parcb'Some; eauto. go.
          - elim H2. 
            (* WF_CSSA extra constraints *)
            exploit fn_jp_use_phib ; eauto; go.
          - (* WF_CSSA : usephicode pc' -> parcopycode pc' *)
            invh use_phicode.
            exploit parcbSome; eauto.
            unfold get_preds.
            eapply index_pred_some_nth in KPRED.
            unfold successors_list in *.
            flatten KPRED.
            eapply nth_error_in; eauto. 
            eapply nth_error_in in KPRED; go. 
            go.
        }
      * assert (Hins: exists i, (fn_code f) ! pc' = Some i) 
        by (eapply fn_code_closed; eauto). 
        destruct Hins as [ins' Hins']. rewrite Hins'.
        invh use_parcopycode.
        { flatten ; simpl.
          - (* WF_CSSA extra constraints *)
            exploit fn_jp_use_parcb' ; eauto; go.
            eapply fn_phicode_inv ; go.
            intro Hcont.
            eelim H2; eauto ; go.          
          - eapply reg_list_live_incl_2; eauto.
            replace r with (parc_src (Iparcopy r dst)) by auto. 
            eapply in_map ; eauto.
        }

  - invh cfg.
    exploit DS.fixpoint_solution; eauto.
    + intros. unfold transfer, transfer_parcb', transfer_parcb in *.
      rewrite H1 ; go.
    + unfold Lout, transfer, transfer_parcb', transfer_parcb in *.
      assert (Hins: exists i, (fn_code f) ! pc' = Some i)
        by (eapply fn_code_closed; eauto). 
      destruct Hins as [ins' Hins']. rewrite Hins'.
      flatten ; simpl.
      * (* ~ def r pc' -> dead OK ; ins' = nop ; In r lv # pc' *)
        { eapply reg_list_dead_not_in; eauto.
          - assert (Eqins': exists s', ins' = Inop s'). 
            { exploit (fn_inop_in_jp f H pc'); go.
              intros [succ Hins].
              allinv; eauto.
            }
            destruct Eqins' as [s' Eqins'] ; subst; auto.
          - intros Hcont. elim H2.
            eapply def_parcopycode; eauto. 
            econstructor; eauto.
            exploit @Utils.map_in_some; eauto.
            intros [[src dst] [Hina Hfa]]. subst; eauto. 
        }
      * (* ins' = nop ; In r lv # pc' *)
        assert (Eqins': exists s', ins' = Inop s').
        { exploit (fn_inop_in_jp f H pc'); go.
          intros [succ Hins].
          allinv; eauto.
        }
        destruct Eqins' as [s' Eqins'] ; subst; auto.
      * eapply reg_list_live_incl; auto.
      * {
          destruct ins'; simpl; go;
          try assert (DIFF: r <> r0) by (intro Hcont; subst; eelim H2; go);
          try solve [ eapply reg_list_live_incl; eauto;
                      (eapply SSARegSet.remove_2; eauto; 
                       intro Hcont ; invh and ; subst; eelim DIFF ; destruct r, r0 ; go)].
          - eapply reg_list_live_incl; eauto.
            eapply SSARegSet.add_2 ; eauto.
          - eapply reg_list_live_incl; eauto.
            destruct s0; simpl.
            + eapply SSARegSet.add_2 ; eauto.
              (eapply SSARegSet.remove_2; eauto; 
               intro Hcont ; invh and ; subst; eelim DIFF ; destruct r, r0 ; go).
            + (eapply SSARegSet.remove_2; eauto; 
               intro Hcont ; invh and ; subst; eelim DIFF ; destruct r, r0 ; go).
          - invh cssaliveout_spec;
              (invh cfg;
               assert (ins0 = (Itailcall s s0 l)) by congruence; subst; go).
          - flatten.
            + subst.
              assert (DIFF: x <> r) by (intro Hcont ; subst ; eelim H2; go).
              eapply reg_list_live_incl; eauto.
              eapply SSARegSet.remove_2; eauto.
            + eapply reg_list_live_incl; eauto.
            + eapply reg_list_live_incl; eauto.
          - eapply SSARegSet.add_2; eauto.
          - invh cssaliveout_spec;
              (invh cfg;
               assert (ins0 = (Ireturn o)) by congruence; subst; go).
        }
Qed.

End WF_LIVE.

Lemma live_cssadom : forall f r pc,
  wf_cssa_function f ->
  cssalive_spec f r pc ->
  reached f pc ->
  cssadom f r pc \/ (pc = (fn_entrypoint f)).
Proof.
  induction 2 ; intros.
  - left.
    exploit exists_def; eauto. 
    intros [dr Hdr]. 
    econstructor 1; eauto. 
    split.
    + eapply fn_strict; eauto.
    + intro Hcont; subst; go.
  - exploit IHcssalive_spec; eauto; go. 
    clear IHcssalive_spec. 
    intros [HC1 | HC2].
    + destruct (peq pc (fn_entrypoint f)); eauto.
      edestruct dsd_pred_njp ; eauto. 
      * intuition. 
      * { repeat invh or; repeat invh and.
          - intuition. 
          - invh cssalive_spec; try intuition.
            eelim fn_entry_pred; go. 
          - invh cssalive_spec; try intuition.
            eelim fn_entry_pred; go.            
        }
    + eelim fn_entry_pred; go. 
  - exploit IHcssalive_spec; eauto; go.
Qed.
