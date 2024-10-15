From compcert Require Import Behaviors Lowerbound Compiler Complements.

Set Implicit Arguments.

Theorem transf_clight2_program_preservation_lbd
    p tp
    (T: transf_clight2_program p = Errors.OK tp) :
  improves (Clight.semantics2 p) (Lowerbound.semantics tp).
Proof.
  apply Complements.transf_clight2_program_preservation_lbd.
  apply transf_clight2_program_match. eauto.
Qed.

Theorem transf_clight2_program_via_SSA_preservation_lbd
    p tp
    (T: transf_clight2_program_via_SSA p = Errors.OK tp) :
  improves (Clight.semantics2 p) (Lowerbound.semantics tp).
Proof.
  apply transf_clight2_program_preservation_ssa_lbd.
  apply transf_clight2_program_via_SSA_match. eauto.
Qed.

Require Import Skeleton ModSem.
Require Import STS2SmallStep.
Require Import ClightPlusgen.
Require Import ClightPlusgenCorrect.
Require Import ClightPlus2ClightProof.

Theorem compile_behavior_improves_lbd
    (clight_prog : Clight.program) (asm : Asm.program)
    (mn: string) (md: Mod.t) (sk_mem: Sk.t)
    (COMP: compile clight_prog mn = Errors.OK md)
    (MEMSKEL: mem_skel clight_prog = Errors.OK sk_mem)
    (COMP': transf_clight2_program clight_prog = Errors.OK asm)
:
    (improves2_program (clightp_sem sk_mem md) (Lowerbound.semantics asm)).
Proof.
  eapply improves2_program_observe_trans.
  eapply single_compile_program_improves; eauto.
  eapply transf_clight2_program_preservation_lbd in COMP'.
  unfold Complements.improves in *. i. hexploit COMP'; eauto.
  i. des. hexploit semantics2to3; eauto. i. des.
  esplits; eauto. eapply observation_improves_trans; eauto.
Qed.

Theorem compile_behavior_improves_via_SSA_lbd
    (clight_prog : Clight.program) (asm : Asm.program)
    (mn: string) (md: Mod.t) (sk_mem: Sk.t)
    (COMP: compile clight_prog mn = Errors.OK md)
    (MEMSKEL: mem_skel clight_prog = Errors.OK sk_mem)
    (COMP': transf_clight2_program_via_SSA clight_prog = Errors.OK asm)
:
    (improves2_program (clightp_sem sk_mem md) (Lowerbound.semantics asm)).
Proof.
  eapply improves2_program_observe_trans.
  eapply single_compile_program_improves; eauto.
  eapply transf_clight2_program_via_SSA_preservation_lbd in COMP'.
  unfold Complements.improves in *. i. hexploit COMP'; eauto.
  i. des. hexploit semantics2to3; eauto. i. des.
  esplits; eauto. eapply observation_improves_trans; eauto.
Qed.