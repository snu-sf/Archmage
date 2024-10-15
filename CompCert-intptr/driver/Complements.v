(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Corollaries of the main semantic preservation theorem. *)

Require Import Classical.
Require Import Coqlib Errors.
Require Import AST Linking Events Smallstep Behaviors.
Require Import Csyntax Csem (* Cstrategy *) Asm.
Require Import Compiler.
Require Import sflib CoqlibC.
Require Import ClightD CsharpminorD.
Require Import Cminor CminorSelD RTL RTLD LTLD LinearD MachD.
Require Import RTLdfsD SSAD CSSAD RTLparD.
Require Import AsmD.

Require Import Simulation.

Set Implicit Arguments.

Definition improves (L1 L2: semantics): Prop := forall obs2
    (BEH: program_observes L2 obs2),
    exists obs1, <<BEH: program_observes L1 obs1>> /\ <<IMPRV: observation_improves obs1 obs2>>.

Global Program Instance improves_PreOrder: PreOrder improves.
Next Obligation.
  ii. esplits; eauto. eapply observation_improves_refl.
Qed.
Next Obligation.
  ii. r in H. r in H0. repeat spc H0. des. specialize (H _ BEH0). des.
  esplits; eauto. eapply observation_improves_trans; eauto.
Qed.

Lemma bsim_improves L1 L2
      (BSIM: Simulation.backward_simulation L1 L2):
    <<IMRPV: improves L1 L2>>.
Proof.
  ii. eapply backward_simulation_observation_improves; eauto.
  eapply backward_to_nostutter_backward_simulation. eauto.
Qed.

Lemma rtc_improves src tgt
    (REL: rtc improves src tgt) :
  improves src tgt.
Proof. induction REL; try refl. etrans; eauto. Qed.

Section SimplLocals.

  Lemma SimplLocals_correct src tgt
      (TRANSF: SimplLocalsproof.match_prog src tgt):
    improves (Clight.semantics1 src) (Clight.semantics2 tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply SimplLocalsproof.transf_program_correct. eauto.
  Qed.

End SimplLocals.

Section Cshmgen.

  Lemma Cshmgen_correct src tgt
      (TRANSF: Cshmgenproof.match_prog src tgt):
    improves (Clight.semantics2 src) (Csharpminor.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply Cshmgenproof.transl_program_correct. eauto.
  Qed.

End Cshmgen.

Section Cminorgen.

  Lemma Cminorgen_correct
        src tgt
        (TRANSF: Cminorgenproof.match_prog src tgt):
    improves (Csharpminor.semantics src) (Cminor.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply Cminorgenproof.transl_program_correct. eauto.
  Qed.

End Cminorgen.

Section Selection.

  Lemma Selection_correct src tgt
      (TRANSF: Selectionproof.match_prog src tgt):
    improves (Cminor.semantics src) (CminorSel.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply Selectionproof.transf_program_correct. eauto.
  Qed.

End Selection.

Section RTLgen.

  Lemma RTLgen_correct src tgt
      (TRANSF: RTLgenproof.match_prog src tgt):
    improves (CminorSel.semantics src) (RTL.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply RTLgenproof.transf_program_correct. eauto.
  Qed.

End RTLgen.

Section Renumber0.

  Lemma Renumber0_correct src tgt
      (TRANSF: Renumberproof.match_prog src tgt):
    improves (RTL.semantics src) (RTL.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply Renumberproof.transf_program_correct. eauto.
  Qed.

End Renumber0.

Section Tailcall.

  Lemma Tailcall_correct src tgt
      (TRANSF: match_if Compopts.optim_tailcalls Tailcallproof.match_prog src tgt):
    rtc improves (RTL.semantics src) (RTL.semantics tgt).
  Proof.
    unfold match_if in *. des_ifs; try refl.
    - apply rtc_once.
      eapply bsim_improves. eapply mixed_to_backward_simulation.
      eapply Tailcallproof.transf_program_correct. eauto.
  Qed.

End Tailcall.


Section Inlining.

  Lemma Inlining_correct src tgt
      (TRANSF: Inliningproof.match_prog src tgt):
    improves (RTL.semantics src) (RTL.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply Inliningproof.transf_program_correct. eauto.
  Qed.

End Inlining.


Section Constprop.

  Lemma Constprop_correct src tgt
      (TRANSF: match_if Compopts.optim_constprop Constpropproof.match_prog src tgt):
    rtc improves (RTL.semantics src) (RTL.semantics tgt).
  Proof.
    unfold match_if in *. des_ifs; try refl.
    - apply rtc_once. eapply bsim_improves. eapply mixed_to_backward_simulation.
      eapply Constpropproof.transf_program_correct. eauto.
  Qed.

End Constprop.



Section Renumber1.

  Lemma Renumber1_correct src tgt
      (TRANSF: match_if Compopts.optim_constprop Renumberproof.match_prog src tgt):
    rtc improves (RTL.semantics src) (RTL.semantics tgt).
  Proof.
    unfold match_if in *. des_ifs; try refl.
    apply rtc_once. eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply Renumberproof.transf_program_correct. eauto.
  Qed.

End Renumber1.

Section CSE.

  Lemma CSE_correct src tgt
        (TRANSF: match_if Compopts.optim_CSE CSEproof.match_prog src tgt):
    rtc improves (RTL.semantics src) (RTL.semantics tgt).
  Proof.
    unfold match_if in *. des_ifs; try refl.
    apply rtc_once. eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply CSEproof.transf_program_correct. eauto.
  Qed.

End CSE.

Section Deadcode.

  Lemma Deadcode_correct src tgt
    (TRANSF: match_if Compopts.optim_redundancy Deadcodeproof.match_prog src tgt):
    rtc improves (RTL.semantics src) (RTL.semantics tgt).
  Proof.
    unfold match_if in *. des_ifs; try refl.
    apply rtc_once. eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply Deadcodeproof.transf_program_correct. eauto.
  Qed.

End Deadcode.

Section Unusedglob.

  Lemma Unusedglob_correct src tgt
      (TRANSF: Unusedglobproof.match_prog src tgt):
    improves (RTL.semantics src) (RTL.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply Unusedglobproof.transf_program_correct. eauto.
  Qed.

End Unusedglob.

Section Allocation.

  Lemma Allocation_correct src tgt
      (TRANSF: Allocproof.match_prog src tgt):
    improves (RTL.semantics src) (LTL.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply Allocproof.transf_program_correct. eauto.
  Qed.

End Allocation.

Section Tunneling.

  Lemma Tunneling_correct src tgt
      (TRANSF: Tunnelingproof.match_prog src tgt):
    improves (LTL.semantics src) (LTL.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply Tunnelingproof.transf_program_correct. eauto.
  Qed.

End Tunneling.

Section Linearize.

  Lemma Linearize_correct src tgt
      (TRANSF: Linearizeproof.match_prog src tgt):
    improves (LTL.semantics src) (Linear.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply Linearizeproof.transf_program_correct. eauto.
  Qed.

End Linearize.

Section CleanupLabels.

  Lemma CleanupLabels_correct src tgt
      (TRANSF: CleanupLabelsproof.match_prog src tgt):
    improves (Linear.semantics src) (Linear.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply CleanupLabelsproof.transf_program_correct. eauto.
  Qed.

End CleanupLabels.

Section Debugvar.

  Lemma Debugvar_correct src tgt
      (TRANSF: match_if Compopts.debug Debugvarproof.match_prog src tgt):
    rtc improves (Linear.semantics src) (Linear.semantics tgt).
  Proof.
    unfold match_if in *. des_ifs; try refl.
    apply rtc_once. eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply Debugvarproof.transf_program_correct. eauto.
  Qed.

End Debugvar.



Section Stacking.

  Lemma return_address_offset_deterministic:
    forall f c ofs ofs',
      Asmgenproof0.return_address_offset f c ofs ->
      Asmgenproof0.return_address_offset f c ofs' ->
      ofs = ofs'.
  Proof.
    i. inv H; inv H0.
    rewrite TF in TF0. inv TF0. rewrite TC in TC0. inv TC0.
    eapply Asmgenproof0.code_tail_unique in TL; eauto.
    assert(Integers.Ptrofs.eq ofs ofs' = true).
    unfold Integers.Ptrofs.eq. rewrite TL. rewrite zeq_true. auto.
    exploit Integers.Ptrofs.eq_spec. rewrite H. auto.
  Qed.

  Lemma Stacking_correct src tgt
      (TRANSF: Stackingproof.match_prog src tgt)
      (COMPILESUCCED: exists final_tgt, Asmgenproof.match_prog tgt final_tgt):
    improves (Linear.semantics src) (Mach.semantics Asmgenproof0.return_address_offset tgt).
  Proof.
    eapply bsim_improves. des. eapply mixed_to_backward_simulation. eapply Stackingproof.transf_program_correct. eauto.
    eapply Asmgenproof.return_address_exists. eauto.
    eapply return_address_offset_deterministic.
  Qed.

End Stacking.

Section Asmgen.

  Lemma Asmgen_correct src tgt
      (TRANSF: Asmgenproof.match_prog src tgt):
    improves (Mach.semantics Asmgenproof0.return_address_offset src) (Asm.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply Asmgenproof.transf_program_correct. eauto.
  Qed.

End Asmgen.

(** SSA optimization Correctness *)

Section RTLnorm.

  Lemma RTLnorm_correct src tgt
      (TRANSF: RTLnormproof.match_prog src tgt):
    improves (RTL.semantics src) (RTL.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply RTLnormproof.transf_program_correct. eauto.
  Qed.

End RTLnorm.

Section RTLdfs.

  Lemma RTLdfs_correct src tgt
    (TRANSF: RTLdfsproof.match_prog src tgt):
    improves (RTL.semantics src) (RTLdfs.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply RTLdfsproof.transf_program_correct. eauto.
  Qed.

End RTLdfs.

Section SSA.

  Lemma SSA_correct src tgt
      (WF: RTLdfsgen.wf_dfs_program src)
      (TRANSF: SSAvalidproof.match_prog src tgt):
    improves (RTLdfs.semantics src) (SSA.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply SSAvalidproof.transf_program_correct; eauto.
  Qed.

End SSA.

Section Copyprop.

  Lemma Copyprop_correct src tgt
      (WF : SSA.wf_ssa_program src)
      (TRANSF: Copypropproof.match_prog src tgt):
    improves (SSA.semantics src) (SSA.semantics tgt).
  Proof.
    exploit Copypropproof.tprog_transf; eauto. i; clarify.
    exploit Copypropproof.transf_program_repeatn; i; des. rewrite H. clear H.
    induction n; ss; i.
    - econs. esplits; eauto. eapply observation_improves_refl.
    - etrans.
      + ii. exploit IHn; eauto.
      + eapply bsim_improves. eapply mixed_to_backward_simulation.
        eapply Copypropproof.transf_program_step_correct.
        eapply Copypropproof.transf_program_step_match.
        generalize n as n'; induction n'; ss.
        eapply Copypropproof.match_prog_step_wf_ssa; eauto.
        eapply Copypropproof.transf_program_step_match.
  Qed.

End Copyprop.

Section Captureprop.

  Lemma Captureprop_correct src tgt
      (TRANSF: Capturepropproof.match_prog src tgt)
      (WF: SSA.wf_ssa_program src):
    improves (SSA.semantics src) (SSA.semantics tgt).
  Proof.
    exploit Capturepropproof.match_prog_repeatn; eauto. i; des.
    remember (Capturepropproof.capture_node_list (prog_defs src)) as l.
    assert (Datatypes.length l = Datatypes.length (prog_defs src)).
    { rewrite Heql. generalize (prog_defs src) as defs. induction defs; ss; ii.
      des_ifs; ss; lia. }
    clear Heql. clear TRANSF.
    generalize dependent l. generalize dependent src. induction n.
    - s; i. inv H. econs; eauto. split; eauto. eapply observation_improves_refl.
    - i. unfold Capturepropproof.repeatn_monad in H. symmetry in H. monadInv H.
      fold (Capturepropproof.repeatn_monad Capturepropproof.transf_program_step n x) in EQ0.
      destruct x. symmetry in EQ0. eapply IHn in EQ0.
      etrans; eauto. eapply bsim_improves. eapply mixed_to_backward_simulation.
      eapply Capturepropproof.transf_program_step_correct; eauto.
      exploit Capturepropproof.transf_program_step_match; eauto.
      eapply Capturepropproof.transf_program_step_wf_ssa; eauto.
      exploit Capturepropproof.transf_program_step_match; eauto.
      destruct p; destruct src.
      eapply Capturepropproof.transf_program_step_len_preserved in EQ; des; ss. lia.
  Qed.

End Captureprop.

Section CSSA.
  Lemma CSSA_correct src tgt
      (WF: SSA.wf_ssa_program src)
      (TRANSF: CSSAproof.match_prog src tgt):
    improves (SSA.semantics src) (CSSA.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply CSSAproof.transf_program_correct; eauto.
  Qed.
  
End CSSA.

Section RTLpar.

  Lemma RTLpar_correct src tgt
    (WF: CSSA.wf_cssa_program src)
    (TRANSF: RTLparproof.match_prog src tgt):
    improves (CSSA.semantics src) (RTLpar.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply RTLparproof.transf_program_correct; eauto.
  Qed.

End RTLpar.

Section RTLparcleanup.
  Lemma RTLparcleanup_correct src tgt
    (TRANSF: RTLparcleanup.match_prog src tgt):
    improves (RTLpar.semantics src) (RTLpar.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply RTLparcleanup.transf_program_correct; eauto.
  Qed.
  
End RTLparcleanup.

Section RTLdpar.
  Lemma RTLdpar_correct src tgt
    (WF: RTLpar.wf_program src)
    (WF': RTLpar.mill_program src)
    (TRANSF: RTLdparproof.match_prog src tgt):
    improves (RTLpar.semantics src) (RTL.semantics tgt).
  Proof.
    eapply bsim_improves. eapply mixed_to_backward_simulation.
    eapply RTLdparproof.transf_program_correct; eauto.
  Qed.
  
End RTLdpar.

Require Import Lowerbound.

Section Lowerbound.
  Lemma Lowerbound_correct prog:
    improves (Asm.semantics prog) (Lowerbound.semantics prog).
  Proof.
    eapply bsim_improves. eapply Lowerbound.lowerbound_correct.
  Qed.
  
End Lowerbound.


(** Composing the [match_prog] relations above, we obtain the relation
  between CompCert C sources and Asm code that characterize CompCert's
  compilation. *)

Definition match_prog_clight: Clight.program -> Asm.program -> Prop :=
  pass_match (compose_passes Clight_to_Asm).

Definition match_prog_clight_ssa: Clight.program -> Asm.program -> Prop :=
  pass_match (compose_passes Clight_to_Asm_ssa).

Definition match_prog_clight2: Clight.program -> Asm.program -> Prop :=
  pass_match (compose_passes Clight2_to_Asm).

Definition match_prog_clight2_ssa: Clight.program -> Asm.program -> Prop :=
  pass_match (compose_passes Clight2_to_Asm_ssa).

Lemma transf_clight2_program_preservation p tp
    (TRANSF: match_prog_clight2 p tp) :
  improves (Clight.semantics2 p) (Asm.semantics tp).
Proof.
  unfold match_prog_clight2, pass_match in TRANSF; simpl in TRANSF.
  Ltac DestructM :=
    match goal with
      [ H: exists p, _ /\ _ |- _ ] =>
      let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
      destruct H as (p & M & MM); clear H
  end.
  repeat DestructM. subst tp.

  etrans. eapply Cshmgen_correct; eauto.
  etrans. eapply Cminorgen_correct; eauto.
  etrans. eapply Selection_correct; eauto.
  etrans. eapply RTLgen_correct; eauto.
  etrans. exploit Tailcall_correct; eauto. intros REL. eapply rtc_improves; eauto.
  etrans. eapply Inlining_correct; eauto.
  etrans. eapply Renumber0_correct; eauto.
  etrans. exploit Constprop_correct; eauto. intros REL. eapply rtc_improves; eauto.
  etrans. exploit Renumber1_correct; eauto. intros REL. eapply rtc_improves; eauto.
  etrans. exploit CSE_correct; eauto. intros REL. eapply rtc_improves; eauto.
  etrans. exploit Deadcode_correct; eauto. intros REL. eapply rtc_improves; eauto.
  etrans. eapply Unusedglob_correct; eauto.
  etrans. eapply Allocation_correct; eauto.
  etrans. eapply Tunneling_correct; eauto.
  etrans. eapply Linearize_correct; eauto.
  etrans. eapply CleanupLabels_correct; eauto.
  etrans. exploit Debugvar_correct; eauto. intros REL. eapply rtc_improves; eauto.
  etrans. eapply Stacking_correct; eauto.
  etrans. eapply Asmgen_correct; eauto. refl.
Qed.

Lemma transf_clight2_program_preservation_ssa p tp
    (TRANSF: match_prog_clight2_ssa p tp) :
  improves (Clight.semantics2 p) (Asm.semantics tp).
Proof.
  unfold match_prog_clight2_ssa, pass_match in TRANSF; simpl in TRANSF.
  Ltac Destructm :=
    match goal with
      [ H: exists p, _ /\ _ |- _ ] =>
      let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
      destruct H as (p & M & MM); clear H
  end.
  repeat Destructm. subst tp.

  etrans. eapply Cshmgen_correct; eauto.
  etrans. eapply Cminorgen_correct; eauto.
  etrans. eapply Selection_correct; eauto.
  etrans. eapply RTLgen_correct; eauto.
  etrans. exploit Tailcall_correct; eauto. intros REL. eapply rtc_improves; eauto.
  etrans. eapply Inlining_correct; eauto.
  etrans. eapply Renumber0_correct; eauto.
  etrans. exploit Constprop_correct; eauto. intros REL. eapply rtc_improves; eauto.
  etrans. exploit Renumber1_correct; eauto. intros REL. eapply rtc_improves; eauto.
  etrans. exploit CSE_correct; try apply M8. intros REL. eapply rtc_improves; eauto.
  etrans. exploit Deadcode_correct; eauto. intros REL. eapply rtc_improves; eauto.
  etrans. eapply Unusedglob_correct; eauto.

  etrans. eapply RTLnorm_correct; eauto.
  etrans. eapply RTLdfs_correct; eauto.
  etrans. eapply SSA_correct; eauto. eapply RTLdfsproof.match_prog_wf_dfs; eauto.
  etrans. eapply Copyprop_correct; eauto.
    eapply SSAvalidproof.match_prog_wf_ssa; eauto.
    eapply RTLdfsproof.match_prog_wf_dfs; eauto.
  etrans. eapply Captureprop_correct; eauto.
    eapply Copypropproof.match_prog_wf_ssa; eauto.
    eapply SSAvalidproof.match_prog_wf_ssa; eauto.
    eapply RTLdfsproof.match_prog_wf_dfs; eauto.
  etrans. eapply CSSA_correct; eauto.
    eapply Capturepropproof.match_prog_wf_ssa; eauto.
    eapply Copypropproof.match_prog_wf_ssa; eauto.
    eapply SSAvalidproof.match_prog_wf_ssa; eauto.
    eapply RTLdfsproof.match_prog_wf_dfs; eauto.
    (* eapply CSSAgenwf.wf_cssa_tprog; eauto. *)
  etrans. eapply RTLpar_correct; eauto.
  (* etrans. eapply RTLpar_correct; eauto. *)
    eapply CSSAgenwf.wf_cssa_tprog; eauto.
    eapply Capturepropproof.match_prog_wf_ssa; eauto.
    eapply Copypropproof.match_prog_wf_ssa; eauto.
    eapply SSAvalidproof.match_prog_wf_ssa; eauto.
    eapply RTLdfsproof.match_prog_wf_dfs; eauto.

  etrans. eapply RTLparcleanup_correct; eauto.
  etrans. eapply RTLdpar_correct; eauto.
  2:eapply RTLparcleanup.is_mill_program; eauto.
    eapply RTLparcleanup.match_prof_wf_program; eauto.
    eapply RTLparproof.is_wf_program; eauto.
    eapply CSSAgenwf.wf_cssa_tprog; eauto.
    eapply Capturepropproof.match_prog_wf_ssa; eauto.
    eapply Copypropproof.match_prog_wf_ssa; eauto.
    eapply SSAvalidproof.match_prog_wf_ssa; eauto.
    eapply RTLdfsproof.match_prog_wf_dfs; eauto.
  
  etrans. eapply Renumber0_correct; eauto.
  etrans. exploit CSE_correct; eauto. intros REL. eapply rtc_improves; eauto.
  etrans. eapply Allocation_correct; eauto.
  etrans. eapply Tunneling_correct; eauto.
  etrans. eapply Linearize_correct; eauto.
  etrans. eapply CleanupLabels_correct; eauto.
  etrans. exploit Debugvar_correct; eauto. intros REL. eapply rtc_improves; eauto.
  etrans. eapply Stacking_correct; eauto.
  etrans. eapply Asmgen_correct; eauto. refl.
Qed.

Lemma transf_clight_program_preservation p tp
    (TRANSF: match_prog_clight p tp) :
  improves (Clight.semantics1 p) (Asm.semantics tp).
Proof.
  unfold match_prog_clight, pass_match in TRANSF; simpl in TRANSF.
  repeat DestructM. subst tp.
  etrans. eapply SimplLocals_correct; eauto.
  etrans. eapply transf_clight2_program_preservation. 2:{ refl. }
  unfold match_prog_clight2, pass_match. ss. esplits; eauto.
Qed.

Lemma transf_clight_program_preservation_ssa p tp
    (TRANSF: match_prog_clight_ssa p tp) :
  improves (Clight.semantics1 p) (Asm.semantics tp).
Proof.
  unfold match_prog_clight_ssa, pass_match in TRANSF; simpl in TRANSF.
  repeat Destructm. subst tp.

  etrans. eapply SimplLocals_correct; eauto.
  etrans. eapply transf_clight2_program_preservation_ssa. 2:{ refl. }
  unfold match_prog_clight2_ssa, pass_match. ss. esplits; eauto.
Qed.

Lemma transf_clight_program_preservation_lbd p tp
    (TRANSF: match_prog_clight p tp) :
  improves (Clight.semantics1 p) (Lowerbound.semantics tp).
Proof.
  hexploit transf_clight_program_preservation; eauto. i.
  etrans; eauto. eapply Lowerbound_correct; eauto.
Qed.

Lemma transf_clight_program_preservation_ssa_lbd p tp
    (TRANSF: match_prog_clight_ssa p tp) :
  improves (Clight.semantics1 p) (Lowerbound.semantics tp).
Proof.
  hexploit transf_clight_program_preservation_ssa; eauto. i.
  etrans; eauto. eapply Lowerbound_correct; eauto.
Qed.

Lemma transf_clight2_program_preservation_lbd p tp
    (TRANSF: match_prog_clight2 p tp) :
  improves (Clight.semantics2 p) (Lowerbound.semantics tp).
Proof.
  hexploit transf_clight2_program_preservation; eauto. i.
  etrans; eauto. eapply Lowerbound_correct; eauto.
Qed.

Lemma transf_clight2_program_preservation_ssa_lbd p tp
    (TRANSF: match_prog_clight2_ssa p tp) :
  improves (Clight.semantics2 p) (Lowerbound.semantics tp).
Proof.
  hexploit transf_clight2_program_preservation_ssa; eauto. i.
  etrans; eauto. eapply Lowerbound_correct; eauto.
Qed.

(** * Extension to separate compilation *)

(** The results above were given in terms of whole-program compilation.
    They also extend to separate compilation followed by linking. *)

Theorem separate_transf_clight_program_correct:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_clight_program cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
    /\ improves (Clight.semantics1 c_program) (Asm.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog_clight c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_clight_program_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog_clight c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply transf_clight_program_preservation; auto.
Qed.

Theorem separate_transf_clight2_program_correct:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_clight2_program cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
    /\ improves (Clight.semantics2 c_program) (Asm.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog_clight2 c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_clight2_program_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog_clight2 c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply transf_clight2_program_preservation; auto.
Qed.

Theorem separate_transf_clight_program_correct_lbd:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_clight_program cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
    /\ improves (Clight.semantics1 c_program) (Lowerbound.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog_clight c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_clight_program_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog_clight c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply transf_clight_program_preservation_lbd; auto.
Qed.

Theorem separate_transf_clight2_program_correct_lbd:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_clight2_program cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
    /\ improves (Clight.semantics2 c_program) (Lowerbound.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog_clight2 c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_clight2_program_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog_clight2 c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply transf_clight2_program_preservation_lbd; auto.
Qed.

Theorem separate_transf_clight_program_via_SSA_correct:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_clight_program_via_SSA cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
   /\ improves (Clight.semantics1 c_program) (Asm.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog_clight_ssa c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_clight_program_via_SSA_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog_clight_ssa c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply transf_clight_program_preservation_ssa; auto.
Qed.

Theorem separate_transf_clight2_program_via_SSA_correct:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_clight2_program_via_SSA cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
   /\ improves (Clight.semantics2 c_program) (Asm.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog_clight2_ssa c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_clight2_program_via_SSA_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog_clight2_ssa c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply transf_clight2_program_preservation_ssa; auto.
Qed.

Theorem separate_transf_clight_program_via_SSA_correct_lbd:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_clight_program_via_SSA cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
   /\ improves (Clight.semantics1 c_program) (Lowerbound.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog_clight_ssa c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_clight_program_via_SSA_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog_clight_ssa c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply transf_clight_program_preservation_ssa_lbd; auto.
Qed.

Theorem separate_transf_clight2_program_via_SSA_correct_lbd:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_clight2_program_via_SSA cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
   /\ improves (Clight.semantics2 c_program) (Lowerbound.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog_clight2_ssa c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_clight2_program_via_SSA_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog_clight2_ssa c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply transf_clight2_program_preservation_ssa_lbd; auto.
Qed.

Section SEPARATE_COMPILATION.

(** The source: a list of C compilation units *)
Variable c_units: nlist Clight.program.

(** The compiled code: a list of Asm compilation units, obtained by separate compilation *)
Variable asm_units: nlist Asm.program.
Hypothesis separate_compilation_succeeds:
  nlist_forall2 (fun cu tcu => transf_clight_program cu = OK tcu) c_units asm_units.

Variable asm_units_SSA: nlist Asm.program.
Hypothesis separate_compilation_succeeds_via_SSA:
  nlist_forall2 (fun cu tcu => transf_clight_program_via_SSA cu = OK tcu) c_units asm_units_SSA.

(** We assume that the source C compilation units can be linked together *)
(*     to obtain a monolithic C program [c_program]. *)
Variable c_program: Clight.program.
Hypothesis source_linking: link_list c_units = Some c_program.

(** Then, linking the Asm units obtained by separate compilation succeeds. *)
Lemma compiled_linking_succeeds:
  { asm_program | link_list asm_units = Some asm_program }.
Proof.
  destruct (link_list asm_units) eqn:E.
- exists p; auto.
- exfalso.
  exploit separate_transf_clight_program_correct; eauto. intros (a & P & Q).
  congruence.
Qed.

Lemma compiled_linking_succeeds_via_SSA:
  { asm_program | link_list asm_units_SSA = Some asm_program }.
Proof.
  destruct (link_list asm_units_SSA) eqn:E.
- exists p; auto.
- exfalso.
  exploit separate_transf_clight_program_via_SSA_correct; eauto. intros (a & P & Q).
  congruence.
Qed.

(** Let asm_program be the result of linking the Asm units. *)
Let asm_program: Asm.program := proj1_sig compiled_linking_succeeds.
Let compiled_linking: link_list asm_units = Some asm_program := proj2_sig compiled_linking_succeeds.

Let asm_program_SSA: Asm.program := proj1_sig compiled_linking_succeeds_via_SSA.
Let compiled_linking_SSA: link_list asm_units_SSA = Some asm_program_SSA := proj2_sig compiled_linking_succeeds_via_SSA.

(** Then, [asm_program] preserves the semantics and the specifications of *)
(*   [c_program], in the following sense. *)
(*   First, every behavior of [asm_program] improves upon one of the possible *)
(*   behaviors of [c_program]. *)

Theorem separate_transf_clight_program_preservation:
  improves (Clight.semantics1 c_program) (Asm.semantics asm_program).
Proof.
  exploit separate_transf_clight_program_correct; eauto. intros (a & P & Q).
  assert (a = asm_program) by congruence. subst a. eauto.
Qed.

Theorem separate_transf_clight_program_preservation_via_SSA:
  improves (Clight.semantics1 c_program) (Asm.semantics asm_program_SSA).
Proof.
  intros. exploit separate_transf_clight_program_via_SSA_correct; eauto. intros (a & P & Q).
  rewrite compiled_linking_SSA in P. clarify.
Qed.

(** As a corollary, if [c_program] is free of undefined behaviors,  *)
(**   the behavior of [asm_program] is one of the possible behaviors of [c_program]. *)

Theorem separate_transf_clight_program_is_refinement:
  (forall pm beh, program_observes (Clight.semantics1 c_program) (Some pm, beh) -> not_wrong beh /\ (pm <> fun _ => None)) ->
  (forall pm beh, program_observes (Asm.semantics asm_program) (Some pm, beh) -> intact beh) ->
  (forall pm_asm beh_asm, program_observes (Asm.semantics asm_program) (Some pm_asm, beh_asm) -> exists pm_c beh_c, program_observes (Clight.semantics1 c_program) (Some pm_c, beh_c) /\ gm_improves pm_c pm_asm /\ behav_rel pm_asm beh_c beh_asm).
Proof.
  intros. exploit separate_transf_clight_program_preservation; eauto. intros (obs' & P & Q).
  destruct obs' as [pm' beh']. des. r in Q. ss. des. r in Q0. des_ifs.
  assert (not_wrong beh'). { exploit H; eauto. i. des; eauto. }
  assert (intact beh_asm). { exploit H0; eauto. }
  exists o, beh'. esplits; eauto. r in Q. des ;eauto; subst; clarify.
Qed.

Theorem separate_transf_clight_program_is_refinement_via_SSA:
  (forall pm beh, program_observes (Clight.semantics1 c_program) (Some pm, beh) -> not_wrong beh /\ (pm <> fun _ => None)) ->
  (forall pm beh, program_observes (Asm.semantics asm_program_SSA) (Some pm, beh) -> intact beh) ->
  (forall pm_asm beh_asm, program_observes (Asm.semantics asm_program_SSA) (Some pm_asm, beh_asm) -> exists pm_c beh_c, program_observes (Clight.semantics1 c_program) (Some pm_c, beh_c) /\ gm_improves pm_c pm_asm /\ behav_rel pm_asm beh_c beh_asm).
Proof.
  intros. exploit separate_transf_clight_program_preservation_via_SSA; eauto. intros (obs' & P & Q).
  destruct obs' as [pm' beh']. des. r in Q. ss. des. r in Q0. des_ifs.
  assert (not_wrong beh'). { exploit H; eauto. i. des; eauto. }
  assert (intact beh_asm). { exploit H0; eauto. }
  exists o, beh'. esplits; eauto. r in Q. des ;eauto; subst; clarify.
Qed.

End SEPARATE_COMPILATION.
