(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Abstract syntax and semantics for IA32 assembly language *)

Require Import Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
Require Import IntPtrRel PointerOp CoqlibC Simulation.
Require Import IntPtrRef Asm.

(** * Abstract syntax *)

(** ** Registers. *)

(** Integer registers. *)

Section RELSEM.

Definition val_add_one (v: val) : val :=
  match v with
  | Vptr b ofs => Vptr b (Ptrofs.add ofs Ptrofs.one)
  | Vlong n => if Archi.ptr64 then Vlong (Int64.add n Int64.one) else Vundef
  | Vint n => if negb Archi.ptr64 then Vint (Int.add n Int.one) else Vundef
  | _ => Vundef
  end.

Definition val_add_ptrofs (v: val) (delta: ptrofs) : val :=
  match v with
  | Vptr b ofs => Vptr b (Ptrofs.add ofs delta)
  | Vlong n => if Archi.ptr64 then Vlong (Int64.add n (Ptrofs.to_int64 delta)) else Vundef
  | Vint n => if negb Archi.ptr64 then Vint (Int.add n (Ptrofs.to_int delta)) else Vundef
  | _ => Vundef
  end.

Section EVAL_BUILTIN_ARG.

Variable A: Type.
Variable ge: Senv.t.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Inductive eval_builtin_arg: builtin_arg A -> val -> Prop :=
  | eval_BA: forall x,
      eval_builtin_arg (BA x) (e x)
  | eval_BA_int: forall n,
      eval_builtin_arg (BA_int n) (Vint n)
  | eval_BA_long: forall n,
      eval_builtin_arg (BA_long n) (Vlong n)
  | eval_BA_float: forall n,
      eval_builtin_arg (BA_float n) (Vfloat n)
  | eval_BA_single: forall n,
      eval_builtin_arg (BA_single n) (Vsingle n)
  | eval_BA_loadstack: forall chunk ofs v,
      Mem.loadv chunk m (val_add_ptrofs sp ofs) = Some v ->
      eval_builtin_arg (BA_loadstack chunk ofs) v
  | eval_BA_addrstack: forall ofs,
      eval_builtin_arg (BA_addrstack ofs) (val_add_ptrofs sp ofs)
  | eval_BA_loadglobal: forall chunk id ofs v,
      Mem.loadv chunk m (Senv.symbol_address ge id ofs) = Some v ->
      eval_builtin_arg (BA_loadglobal chunk id ofs) v
  | eval_BA_addrglobal: forall id ofs,
      eval_builtin_arg (BA_addrglobal id ofs) (Senv.symbol_address ge id ofs)
  | eval_BA_splitlong: forall hi lo vhi vlo,
      eval_builtin_arg hi vhi -> eval_builtin_arg lo vlo ->
      eval_builtin_arg (BA_splitlong hi lo) (Val.longofwords vhi vlo)
  | eval_BA_addptr: forall a1 a2 v1 v2,
      eval_builtin_arg a1 v1 -> eval_builtin_arg a2 v2 ->
      eval_builtin_arg (BA_addptr a1 a2)
                       (if Archi.ptr64 then Val.addl v1 v2 else Val.add v1 v2).

Definition eval_builtin_args (al: list (builtin_arg A)) (vl: list val) : Prop :=
  list_forall2 eval_builtin_arg al vl.

Lemma eval_builtin_arg_determ:
  forall a v, eval_builtin_arg a v -> forall v', eval_builtin_arg a v' -> v' = v.
Proof.
  induction 1; intros v' EV; inv EV; try congruence.
  f_equal; eauto.
  apply IHeval_builtin_arg1 in H3. apply IHeval_builtin_arg2 in H5. subst; auto.
Qed.

Lemma eval_builtin_args_determ:
  forall al vl, eval_builtin_args al vl -> forall vl', eval_builtin_args al vl' -> vl' = vl.
Proof.
  induction 1; intros v' EV; inv EV; f_equal; eauto using eval_builtin_arg_determ.
Qed.

End EVAL_BUILTIN_ARG.

Variable ge: genv.

Definition nextinstr (rs: regset) :=
  rs#PC <- (val_add_one (rs#PC)).

Definition nextinstr_nf (rs: regset) : regset :=
  nextinstr (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) rs).

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match Mem.to_ptr (rs#PC) m with
      | Some (Vptr b ofs) => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _ => Stuck
    end
  end.

(** Auxiliaries for memory accesses. *)

Definition exec_load (chunk: memory_chunk) (m: mem)
                     (a: addrmode) (rs: regset) (rd: preg) :=
  match Mem.loadv chunk m (eval_addrmode ge a rs) with
  | Some v => Next (nextinstr_nf (rs#rd <- v)) m
  | None => Stuck
  end.

Definition exec_store (chunk: memory_chunk) (m: mem)
                      (a: addrmode) (rs: regset) (r1: preg)
                      (destroyed: list preg) :=
  match Mem.storev chunk m (eval_addrmode ge a rs) (rs r1) with
  | Some m' => Next (nextinstr_nf (undef_regs destroyed rs)) m'
  | None => Stuck
  end.

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  (** Moves *)
  | Pmov_rr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmovl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vint n))) m
  | Pmovq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vlong n))) m
  | Pmov_rs rd id =>
      Next (nextinstr_nf (rs#rd <- (Genv.symbol_address ge id Ptrofs.zero))) m
  | Pmovl_rm rd a =>
      exec_load Mint32 m a rs rd
  | Pmovq_rm rd a =>
      exec_load Mint64 m a rs rd
  | Pmovl_mr a r1 =>
      exec_store Mint32 m a rs r1 nil
  | Pmovq_mr a r1 =>
      exec_store Mint64 m a rs r1 nil
  | Pmovsd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmovsd_fi rd n =>
      Next (nextinstr (rs#rd <- (Vfloat n))) m
  | Pmovsd_fm rd a =>
      exec_load Mfloat64 m a rs rd
  | Pmovsd_mf a r1 =>
      exec_store Mfloat64 m a rs r1 nil
  | Pmovss_fi rd n =>
      Next (nextinstr (rs#rd <- (Vsingle n))) m
  | Pmovss_fm rd a =>
      exec_load Mfloat32 m a rs rd
  | Pmovss_mf a r1 =>
      exec_store Mfloat32 m a rs r1 nil
  | Pfldl_m a =>
      exec_load Mfloat64 m a rs ST0
  | Pfstpl_m a =>
      exec_store Mfloat64 m a rs ST0 (ST0 :: nil)
  | Pflds_m a =>
      exec_load Mfloat32 m a rs ST0
  | Pfstps_m a =>
      exec_store Mfloat32 m a rs ST0 (ST0 :: nil)
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
      exec_store Mint8unsigned m a rs r1 nil
  | Pmovw_mr a r1 =>
      exec_store Mint16unsigned m a rs r1 nil
  | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1))) m
  | Pmovzb_rm rd a =>
      exec_load Mint8unsigned m a rs rd
  | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1))) m
  | Pmovsb_rm rd a =>
      exec_load Mint8signed m a rs rd
  | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1))) m
  | Pmovzw_rm rd a =>
      exec_load Mint16unsigned m a rs rd
  | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1))) m
  | Pmovsw_rm rd a =>
      exec_load Mint16signed m a rs rd
  | Pmovzl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofintu rs#r1))) m
  | Pmovsl_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.longofint rs#r1))) m
  | Pmovls_rr rd =>
      Next (nextinstr (rs#rd <- (Val.loword rs#rd))) m
  | Pcvtsd2ss_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1))) m
  | Pcvtss2sd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.floatofsingle rs#r1))) m
  | Pcvttsd2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intoffloat rs#r1)))) m
  | Pcvtsi2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofint rs#r1)))) m
  | Pcvttss2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intofsingle rs#r1)))) m
  | Pcvtsi2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleofint rs#r1)))) m
  | Pcvttsd2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longoffloat rs#r1)))) m
  | Pcvtsl2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatoflong rs#r1)))) m
  | Pcvttss2sl_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.longofsingle rs#r1)))) m
  | Pcvtsl2ss_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.singleoflong rs#r1)))) m
  (** Integer arithmetic *)
  | Pleal rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode32 ge a rs))) m
  | Pleaq rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode64 ge a rs))) m
  | Pnegl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd))) m
  | Pnegq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.negl rs#rd))) m
  | Paddl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.add rs#rd (Vint n)))) m
  | Paddq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.addl rs#rd (Vlong n)))) m
  | Psubl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1))) m
  | Psubq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.subl rs#rd rs#r1))) m
  | Psubp_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (psub_join_asm m rs#rd rs#r1))) m
  | Pimull_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1))) m
  | Pimulq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd rs#r1))) m
  | Pimull_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Vint n)))) m
  | Pimulq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mull rs#rd (Vlong n)))) m
  | Pimull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhs rs#RAX rs#r1))) m
  | Pimulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhs rs#RAX rs#r1))) m
  | Pmull_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mul rs#RAX rs#r1)
                            #RDX <- (Val.mulhu rs#RAX rs#r1))) m
  | Pmulq_r r1 =>
      Next (nextinstr_nf (rs#RAX <- (Val.mull rs#RAX rs#r1)
                            #RDX <- (Val.mullhu rs#RAX rs#r1))) m
  | Pcltd =>
      Next (nextinstr_nf (rs#RDX <- (Val.shr rs#RAX (Vint (Int.repr 31))))) m
  | Pcqto =>
      Next (nextinstr_nf (rs#RDX <- (Val.shrl rs#RAX (Vint (Int.repr 63))))) m
  | Pdivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pdivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmodu2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivl r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vint nh, Vint nl, Vint d =>
          match Int.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vint q) #RDX <- (Vint r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pidivq r1 =>
      match rs#RDX, rs#RAX, rs#r1 with
      | Vlong nh, Vlong nl, Vlong d =>
          match Int64.divmods2 nh nl d with
          | Some(q, r) => Next (nextinstr_nf (rs#RAX <- (Vlong q) #RDX <- (Vlong r))) m
          | None => Stuck
          end
      | _, _, _ => Stuck
      end
  | Pandl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1))) m
  | Pandq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd rs#r1))) m
  | Pandl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd (Vint n)))) m
  | Pandq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.andl rs#rd (Vlong n)))) m
  | Porl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1))) m
  | Porq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd rs#r1))) m
  | Porl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd (Vint n)))) m
  | Porq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.orl rs#rd (Vlong n)))) m
  | Pxorl_r rd =>
      Next (nextinstr_nf (rs#rd <- Vzero)) m
  | Pxorq_r rd =>
      Next (nextinstr_nf (rs#rd <- (Vlong Int64.zero))) m
  | Pxorl_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1))) m
  | Pxorq_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd rs#r1))) m
  | Pxorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Vint n)))) m
  | Pxorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xorl rs#rd (Vlong n)))) m
  | Pnotl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notint rs#rd))) m
  | Pnotq rd =>
      Next (nextinstr_nf (rs#rd <- (Val.notl rs#rd))) m
  | Psall_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd rs#RCX))) m
  | Psalq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd rs#RCX))) m
  | Psall_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd (Vint n)))) m
  | Psalq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shll rs#rd (Vint n)))) m
  | Pshrl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#RCX))) m
  | Pshrq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd rs#RCX))) m
  | Pshrl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Vint n)))) m
  | Pshrq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrlu rs#rd (Vint n)))) m
  | Psarl_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#RCX))) m
  | Psarq_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd rs#RCX))) m
  | Psarl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Vint n)))) m
  | Psarq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shrl rs#rd (Vint n)))) m
  | Pshld_ri rd r1 n =>
      Next (nextinstr_nf
              (rs#rd <- (Val.or (Val.shl rs#rd (Vint n))
                                (Val.shru rs#r1 (Vint (Int.sub Int.iwordsize n)))))) m
  | Prorl_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Vint n)))) m
  | Prorq_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.rorl rs#rd (Vint n)))) m
  | Pcmpl_rr r1 r2 =>
      Next (nextinstr (compare_ints (rs r1) (rs r2) rs m)) m
  | Pcmpq_rr r1 r2 =>
      Next (nextinstr (compare_longs (rs r1) (rs r2) rs m)) m
  | Pcmpl_ri r1 n =>
      Next (nextinstr (compare_ints (rs r1) (Vint n) rs m)) m
  | Pcmpq_ri r1 n =>
      Next (nextinstr (compare_longs (rs r1) (Vlong n) rs m)) m
  | Ptestl_rr r1 r2 =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs m)) m
  | Ptestq_rr r1 r2 =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (rs r2)) (Vlong Int64.zero) rs m)) m
  | Ptestl_ri r1 n =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (Vint n)) Vzero rs m)) m
  | Ptestq_ri r1 n =>
      Next (nextinstr (compare_longs (Val.andl (rs r1) (Vlong n)) (Vlong Int64.zero) rs m)) m
  | Pcmov c rd r1 =>
      let v :=
        match eval_testcond c rs with
        | Some b => if b then rs#r1 else rs#rd
        | None   => Vundef
      end in
      Next (nextinstr (rs#rd <- v)) m
  | Psetcc c rd =>
      Next (nextinstr (rs#rd <- (Val.of_optbool (eval_testcond c rs)))) m
  (** Arithmetic operations over double-precision floats *)
  | Paddd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#rd rs#r1))) m
  | Psubd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#rd rs#r1))) m
  | Pmuld_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#rd rs#r1))) m
  | Pdivd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#rd rs#r1))) m
  | Pnegd rd =>
      Next (nextinstr (rs#rd <- (Val.negf rs#rd))) m
  | Pabsd rd =>
      Next (nextinstr (rs#rd <- (Val.absf rs#rd))) m
  | Pcomisd_ff r1 r2 =>
      Next (nextinstr (compare_floats (rs r1) (rs r2) rs)) m
  | Pxorpd_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vfloat Float.zero))) m
  (** Arithmetic operations over single-precision floats *)
  | Padds_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addfs rs#rd rs#r1))) m
  | Psubs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subfs rs#rd rs#r1))) m
  | Pmuls_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulfs rs#rd rs#r1))) m
  | Pdivs_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divfs rs#rd rs#r1))) m
  | Pnegs rd =>
      Next (nextinstr (rs#rd <- (Val.negfs rs#rd))) m
  | Pabss rd =>
      Next (nextinstr (rs#rd <- (Val.absfs rs#rd))) m
  | Pcomiss_ff r1 r2 =>
      Next (nextinstr (compare_floats32 (rs r1) (rs r2) rs)) m
  | Pxorps_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vsingle Float32.zero))) m
  (** Branches and calls *)
  | Pjmp_l lbl =>
      goto_label f lbl rs m
  | Pjmp_s id sg =>
      Next (rs#PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pjmp_r r sg =>
      Next (rs#PC <- (rs r)) m
  | Pjcc cond lbl =>
      match eval_testcond cond rs with
      | Some true => goto_label f lbl rs m
      | Some false => Next (nextinstr rs) m
      | None => Stuck
      end
  | Pjcc2 cond1 cond2 lbl =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => goto_label f lbl rs m
      | Some _, Some _ => Next (nextinstr rs) m
      | _, _ => Stuck
      end
  | Pjmptbl r tbl =>
      match rs#r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs #RAX <- Vundef #RDX <- Vundef) m
          end
      | _ => Stuck
      end
  | Pcall_s id sg =>
      (* make Val.offset_ptr to val_add_one *)
      Next (rs#RA <- (val_add_one rs#PC) #PC <- (Genv.symbol_address ge id Ptrofs.zero)) m
  | Pcall_r r sg =>
      Next (rs#RA <- (val_add_one rs#PC) #PC <- (rs r)) m
  | Pret =>
      Next (rs#PC <- (rs#RA)) m
  (** Saving and restoring registers *)
  | Pmov_rm_a rd a =>
      exec_load (if Archi.ptr64 then Many64 else Many32) m a rs rd
  | Pmov_mr_a a r1 =>
      exec_store (if Archi.ptr64 then Many64 else Many32) m a rs r1 nil
  | Pmovsd_fm_a rd a =>
      exec_load Many64 m a rs rd
  | Pmovsd_mf_a a r1 =>
      exec_store Many64 m a rs r1 nil
  (** Pseudo-instructions *)
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Pallocframe sz ofs_ra ofs_link =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := Vptr stk Ptrofs.zero in
      match Mem.storev Mptr m1 (Val.offset_ptr sp ofs_link) rs#RSP with
      | None => Stuck
      | Some m2 =>
          match Mem.storev Mptr m2 (Val.offset_ptr sp ofs_ra) rs#RA with
          | None => Stuck
          | Some m3 => Next (nextinstr (rs #RAX <- (rs#RSP) #RSP <- sp)) m3
          end
      end
  | Pfreeframe sz ofs_ra ofs_link =>
      match Mem.loadv Mptr m (val_add_ptrofs rs#RSP ofs_ra) with
      | None => Stuck
      | Some ra =>
          match Mem.loadv Mptr m (val_add_ptrofs rs#RSP ofs_link) with
          | None => Stuck
          | Some sp =>
              match to_ptr (val_add_ptrofs rs#RSP ofs_ra) m with
              | Vptr stk ofs =>
                  match Mem.free m stk 0 sz with
                  | None => Stuck
                  | Some m' => Next (nextinstr (rs#RSP <- sp #RA <- ra)) m'
                  end
              | _ => Stuck
              end
          end
      end
  | Pbuiltin ef args res =>
      Stuck                             (**r treated specially below *)
  (** The following instructions and directives are not generated *)
(*       directly by [Asmgen], so we do not model them. *)
  | Padcl_ri _ _
  | Padcl_rr _ _
  | Paddl_mi _ _
  | Paddl_rr _ _
  | Pbsfl _ _
  | Pbsfq _ _
  | Pbsrl _ _
  | Pbsrq _ _
  | Pbswap64 _
  | Pbswap32 _
  | Pbswap16 _
  | Pcfi_adjust _
  | Pfmadd132 _ _ _
  | Pfmadd213 _ _ _
  | Pfmadd231 _ _ _
  | Pfmsub132 _ _ _
  | Pfmsub213 _ _ _
  | Pfmsub231 _ _ _
  | Pfnmadd132 _ _ _
  | Pfnmadd213 _ _ _
  | Pfnmadd231 _ _ _
  | Pfnmsub132 _ _ _
  | Pfnmsub213 _ _ _
  | Pfnmsub231 _ _ _
  | Pmaxsd _ _
  | Pminsd _ _
  | Pmovb_rm _ _
  | Pmovq_rf _ _
  | Pmovsq_rm _ _
  | Pmovsq_mr _ _
  | Pmovsb
  | Pmovsw
  | Pmovw_rm _ _
  | Pnop
  | Prep_movsl
  | Psbbl_rr _ _
  | Psqrtsd _ _
  | Psubl_ri _ _
  | Psubq_ri _ _ => Stuck
  end.

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (val_add_ptrofs (rs (IR RSP)) (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.

(** Execution of the instruction at [rs#PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive astep: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      Mem.to_ptr (rs PC) m = Some (Vptr b ofs) ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      astep (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      Mem.to_ptr (rs PC) m = Some (Vptr b ofs) ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args PregEq.t ge rs (rs RSP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr_nf
             (set_res res vres
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      astep (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      Mem.to_ptr (rs PC) m = Some (Vptr b Ptrofs.zero) ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      external_call ef ge args m t res m' ->
      rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs)) #PC <- (rs RA) ->
      astep (State rs m) t (State rs' m').

Definition goto_label_state (s: Asm.state) : Prop :=
  match s with
  | Asm.State rs m => match (rs PC) with
                     | Vptr b ofs => match Genv.find_funct_ptr ge b with
                                    | Some (Internal f) =>
                                        match find_instr (Ptrofs.unsigned ofs) f.(fn_code) with
                                        | Some i => match i with
                                                   | Pjmp_l _ | Pjcc _ _ | Pjcc2 _ _ _ | Pjmptbl _ _ => True
                                                   | _ => False
                                                   end
                                        | _ => False
                                        end
                                    | _ => False
                                    end
                     | _ => False
                     end
  end.

Definition register_concretizer (m: mem) (rs rs': regset) : Prop :=
  forall r, match rs#r with
       | Vptr b ofs =>
           if Mem.is_valid m b
           then val_intptr m (Vptr b ofs) (rs'#r) /\ is_int_value (rs'#r)
           (* invalid pointer: ill-formed register *)
           else rs#r = rs'#r
       | _ => rs#r = rs'#r
       end.

Definition register_concretizer_func (m: mem) (v: val) : val :=
  match v with
  | Vptr b ofs => if Mem.is_valid m b
                 then (match Mem.to_int (Vptr b ofs) m with
                       | Some v => v
                       | _ => Vundef
                       end)
                 else v
  | _ => v
  end.
             
Lemma register_concretizer_exists m rs
  (ALLCONC: forall b (VLD: Mem.valid_block m b), exists addr, m.(Mem.mem_concrete) ! b = Some addr):
  exists rs', register_concretizer m rs rs'.
Proof.
  exists (Pregmap.map (register_concretizer_func m) rs). ii. des_ifs; try by (unfold Pregmap.map; rewrite Heq; ss).
  - unfold Pregmap.map. rewrite Heq. ss. rewrite Heq0.
    rewrite <- Mem.valid_block_iff_is_valid in Heq0. exploit ALLCONC; eauto. i. des.
    unfold Mem.ptr2int. des_ifs_safe; ss. des_ifs. split; eauto.
    econs; eauto. ss. unfold Mem.ptr2int. rewrite Heq1. des_ifs.
  - unfold Pregmap.map. rewrite Heq. ss. rewrite Heq0. eauto.
Qed.

Inductive cstep : state -> state -> Prop :=
| cstep_intros
    m m' m'' rs rs'
    (CONC: memory_block_concretize m m')
    (CCONC: memory_concretize_contents m' m'')
    (RCONC: register_concretizer m'' rs rs'):
  cstep (State rs m) (State rs' m'')
.

Inductive step : state -> trace -> state -> Prop :=
| step_intro
    st tr st' st''
    (ASTEP: astep st tr st')
    (CSTEP: cstep st' st''):
  step st tr st''
| step_oom
    st tr st' tr'
    (ASTEP: astep st tr st')
    (COOM: forall st'', ~ cstep st' st'')
    (OOMTR: tr' = tr ++ [Event_pterm]) :
  step st tr' st'.

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      Genv.init_mem p = Some m0 ->
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # RA <- Vnullptr
        # RSP <- Vnullptr in
      initial_state p (State rs0 m0).

Definition function_length (f: function) : Z :=
  let len := Zlength f.(fn_code) in
  if zeq len 0 then 1 else len.

Section LBDINIT.

Variable p: program.
Let ge := Genv.globalenv p.

Definition realloc_global (m: mem) (b:block): option mem :=
  match Genv.find_funct_ptr ge b with
  | Some (Internal f) => Mem.nonempty_alloc m b 0 (function_length f)
  | Some (External ef) => Some m
  | _ => Some m
  end.


Inductive _realloc_globals : mem -> block -> mem -> Prop :=
| _realloc_globals_1
    b m m'
    (BLK: b = 1%positive)
    (RA: realloc_global m 1%positive = Some m'):
  _realloc_globals m b m'
| _realloc_globals_pos
    m b m' m''
    (BLK: b <> 1%positive)
    (RA: realloc_global m b = Some m')
    (RA: _realloc_globals m' (b - 1)%positive m''):
  _realloc_globals m b m''.

Definition realloc_globals (m m': mem) : Prop :=
  _realloc_globals m (m.(Mem.nextblock) - 1)%positive m'.

Lemma realloc_globals_determ
    m m' m''
    (RA1: realloc_globals m m')
    (RA2: realloc_globals m m''):
  m' = m''.
Proof.
  unfold realloc_globals in *. des_ifs.
  remember ((Mem.nextblock m - 1)%positive). (* clear n. *)
  clear Heqp0. revert RA2 RA1. revert m m' m''. revert p0.
  induction p0 using positive_Peano_ind; i.
  - inv RA1; inv RA2; clarify.
  - inv RA1; inv RA2; try by (exfalso; eapply Pos.succ_not_1; eauto).
    Eq.
    assert ((Pos.succ p0 - 1 = p0)%positive).
    { lia. }
    erewrite H in *. eapply IHp0; eauto.
Qed.

End LBDINIT.

Inductive initial_state_r (p: program): state -> Prop :=
| initial_state_r_intro rs0 m0 m'
    (INIT: initial_state p (State rs0 m0))
    (REA: realloc_globals p m0 m'):
  initial_state_r p (State rs0 m').

Inductive glob_capture (p: program) : state -> state -> Prop :=
  | glob_capture_intro
      rs m pbs m'
      (NONSTATIC: Genv.non_static_glob (Genv.globalenv p) (Genv.genv_public (Genv.globalenv p)) = pbs)
      (CAPTURE: Genv.capture_init_mem m pbs m') :
    glob_capture p (State rs m) (State rs m').

Inductive glob_capture_c (p: program) : state -> state -> Prop :=
| glob_capture_c_intro
    s s' s''
    (GC: glob_capture p s s')
    (CS: cstep s' s''):
  glob_capture_c p s s''.

Definition state_mem (st: state) : mem :=
  match st with
  | State _ m => m
  end.

Definition concrete_snapshot (ge: Senv.t) (st: state) (id: ident) : option Z :=
  if Senv.public_symbol ge id
  then (match Senv.find_symbol ge id with
        | Some b => Maps.PTree.get b (state_mem st).(Mem.mem_concrete)
        | None => None
        end
    )
  else None.

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs#PC = Vnullptr ->
      rs#RAX = Vint r ->
      final_state (State rs m) r.

(** Non-deterministic external state *)

Definition is_external (ge: genv) (st: state): Prop := False.

Definition semantics (p: program) :=
  Semantics step (initial_state_r p) (glob_capture_c p) (concrete_snapshot (Genv.globalenv p)) final_state is_external (Genv.globalenv p).

(* move to Memory.v *)
Lemma nonempty_nonempty_alloc
    m b lo hi m' k
    (LT: lo < hi)
    (CONC: Mem.is_concrete m b = false)
    (NA: Mem.nonempty_alloc m b lo hi = Some m'):
  Mem.range_perm m' b lo hi k Nonempty
/\ (forall ofs k, (lo <= ofs < hi) -> forall p, Mem.perm m' b ofs k p -> p = Nonempty).
Proof.
  unfold Mem.nonempty_alloc in NA. des_ifs.
  unfold Mem.range_perm, Mem.perm. ss. erewrite CONC. splits.
  { i. erewrite PMap.gss; eauto. des_ifs.
    2:{ exfalso. clear - H Heq.
        eapply andb_false_iff in Heq. des.
        - eapply proj_sumbool_false in Heq. lia.
        - eapply proj_sumbool_false in Heq. lia. }
    ss. econs. }
  ii. erewrite PMap.gss in H0. des_ifs. inv H0; eauto.
Qed.

Lemma function_length_pos f: function_length f > 0.
Proof.
  unfold function_length. des_ifs. induction (fn_code f).
  - rewrite Zlength_nil in n. clarify.
  - rewrite Zlength_cons. destruct c; ss. lia.
Qed.    

Lemma nonempty_realloc_global
    p m b m' k f
    (CONC: Mem.is_concrete m b = false)
    (FUNC: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal f))
    (RA: realloc_global p m b = Some m'):
  Mem.range_perm m' b 0 (function_length f) k Nonempty
/\ (forall ofs k, (0 <= ofs < function_length f) -> forall p, Mem.perm m' b ofs k p -> p = Nonempty).
    (* (forall p, Mem.range_perm m' b 0 (function_length f) k p -> p = Nonempty). *)
Proof.
  unfold realloc_global in RA. unfold fundef in *.
  erewrite FUNC in RA. eapply nonempty_nonempty_alloc; eauto.
  specialize (function_length_pos f). lia.
Qed.

Lemma nonempty_realloc_global_neq
    p m b m' b'
    (NEQ: b <> b')
    (RA: realloc_global p m b = Some m'):
  m.(Mem.mem_access)!!b' = m'.(Mem.mem_access)!!b'.
Proof.
  unfold realloc_global in RA. des_ifs.
  unfold Mem.nonempty_alloc in RA. des_ifs. ss.
  des_ifs; eauto. erewrite PMap.gso; eauto.
Qed.

Lemma nonempty_realloc_global_not_func
    p m b m' b'
    (FUNC: Genv.find_funct_ptr (Genv.globalenv p) b = None)
    (RA: realloc_global p m b' = Some m'):
  m.(Mem.mem_access)!!b = m'.(Mem.mem_access)!!b.
Proof.
  destruct (peq b' b); cycle 1.
  { eapply nonempty_realloc_global_neq; eauto. }
  subst. unfold realloc_global in RA.
  unfold fundef in *. rewrite FUNC in RA. clarify.
Qed.

Lemma nonempty_realloc_global_external
    p m b m' b' ef
    (FUNC: Genv.find_funct_ptr (Genv.globalenv p) b = Some (External ef))
    (RA: realloc_global p m b' = Some m'):
  m.(Mem.mem_access)!!b = m'.(Mem.mem_access)!!b.
Proof.
  destruct (peq b' b); cycle 1.
  { eapply nonempty_realloc_global_neq; eauto. }
  subst. unfold realloc_global in RA.
  unfold fundef in *. rewrite FUNC in RA. clarify.
Qed.

Lemma nonempty_realloc_globals_not_func_aux
    p m m' b bdd
    (FUNC: Genv.find_funct_ptr (Genv.globalenv p) b = None)
    (RA: _realloc_globals p m bdd m'):
  m.(Mem.mem_access)!!b = m'.(Mem.mem_access)!!b.
Proof.
  ginduction RA; i.
  { eapply nonempty_realloc_global_not_func; eauto. }
  exploit nonempty_realloc_global_not_func; eauto. i.
  rewrite H. eapply IHRA. eauto.
Qed.

Lemma nonempty_realloc_globals_external_aux
    p m m' b bdd ef
    (FUNC: Genv.find_funct_ptr (Genv.globalenv p) b = Some (External ef))
    (RA: _realloc_globals p m bdd m'):
  m.(Mem.mem_access)!!b = m'.(Mem.mem_access)!!b.
Proof.
  ginduction RA; i.
  { eapply nonempty_realloc_global_external; eauto. }
  exploit nonempty_realloc_global_external; eauto. i.
  rewrite H. eapply IHRA. eauto.
Qed.

Lemma nonempty_realloc_globals_not_range
    p m m' b bdd
    (RANGE: (b > bdd)%positive)
    (RA: _realloc_globals p m bdd m'):
  m.(Mem.mem_access)!!b = m'.(Mem.mem_access)!!b.
Proof.
  ginduction RA; i.
  { assert (b0 <> b) by lia.
    subst. eapply nonempty_realloc_global_neq; eauto. }
  assert (b <> b0) by lia.
  exploit nonempty_realloc_global_neq; eauto. i.
  rewrite H0. eapply IHRA. lia.
Qed.

Lemma nonempty_realloc_globals_not_func
    p m m' b
    (FUNC: Genv.find_funct_ptr (Genv.globalenv p) b = None)
    (RA: realloc_globals p m m'):
  m.(Mem.mem_access)!!b = m'.(Mem.mem_access)!!b.
Proof. eapply nonempty_realloc_globals_not_func_aux; eauto. Qed.

Lemma nonempty_realloc_globals_external
    p m m' b ef
    (FUNC: Genv.find_funct_ptr (Genv.globalenv p) b = Some (External ef))
    (RA: realloc_globals p m m'):
  m.(Mem.mem_access)!!b = m'.(Mem.mem_access)!!b.
Proof. eapply nonempty_realloc_globals_external_aux; eauto. Qed.

Lemma nonempty_realloc_globals_aux
    p m m' b bdd f k
    (LOGICAL: forall b, m.(Mem.mem_concrete) ! b = None)
    (FUNC: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal f))
    (RANGE: (b <= bdd)%positive)
    (RA: _realloc_globals p m bdd m'):
  Mem.range_perm m' b 0 (function_length f) k Nonempty
/\ (forall ofs k, (0 <= ofs < function_length f) -> forall p, Mem.perm m' b ofs k p -> p = Nonempty).
Proof.
  induction RA.
  { subst. assert (b = 1%positive) by lia.
    subst. eapply nonempty_realloc_global; eauto.
    specialize (LOGICAL (1%positive)). unfold Mem.is_concrete.
    rewrite LOGICAL. auto. }
  destruct (peq b b0).
  - subst b0. exploit nonempty_realloc_global; eauto.
    { unfold Mem.is_concrete. specialize (LOGICAL b). rewrite LOGICAL. eauto. }
    instantiate (1:=k).
    exploit nonempty_realloc_globals_not_range; try eapply RA0.
    { instantiate (1:=b). lia. }
    i. des. unfold Mem.range_perm, Mem.perm in H0, H1.
    erewrite H in H0, H1. eauto.
  - exploit IHRA.
    { unfold realloc_global in RA. des_ifs. eapply Mem.nonempty_alloc_concrete in RA.
      rewrite <- RA; eauto. }
    { lia. }
    i. des. split; eauto.
Qed.

Lemma nonempty_realloc_globals
    p m m' b f k
    (LOGICAL: forall b, m.(Mem.mem_concrete) ! b = None)
    (FUNC: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal f))
    (VLD: Mem.valid_block m b)
    (RA: realloc_globals p m m'):
  Mem.range_perm m' b 0 (function_length f) k Nonempty
/\ (forall ofs k, (0 <= ofs < function_length f) -> forall p, Mem.perm m' b ofs k p -> p = Nonempty).
  (* /\ (forall p, Mem.range_perm m' b 0 (function_length f) k p -> p = Nonempty). *)
Proof.
  unfold realloc_globals in RA.
  eapply nonempty_realloc_globals_aux; eauto.
  unfold Mem.valid_block in VLD. clear -VLD.
  unfold Plt in VLD. lia.
Qed.
  
Lemma fn_code_length
  f (NOTNIL: fn_code f <> []):
  Zlength (fn_code f) = function_length f.
Proof.
  unfold function_length. remember (fn_code f). clear Heqc.
  destruct c;ss. des_ifs. rewrite Zlength_correct in e. ss.
Qed.

Lemma find_instr_range
    ofs l i
    (FIN : find_instr ofs l = Some i):
  0 <= ofs < Zlength l /\ Zlength l > 0.
Proof.
  ginduction l; ss; i.
  des_ifs; ss.
  - erewrite Zlength_cons. erewrite Zlength_correct. split; lia.
  - exploit IHl; eauto. i. des. split.
    2:{ erewrite Zlength_cons. lia. }
    split; try lia. erewrite Zlength_cons. lia.
Qed.

Lemma find_instr_range_function
    ofs f i
    (FIN : find_instr ofs (fn_code f) = Some i):
  0 <= ofs < function_length f.
Proof.
  exploit find_instr_range; eauto. intros (RANGE & POS).
  rewrite fn_code_length in RANGE; eauto. destruct (fn_code f); ss.
Qed.

Lemma initial_state_r_permission1
    p rs m b ofs f i k
    (INIT: initial_state_r p (State rs m))
    (FUNC: Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal f))
    (IN: find_instr ofs f.(fn_code) = Some i):
  Mem.perm m b ofs k Nonempty
/\ (forall k p, Mem.perm m b ofs k p -> p = Nonempty).
Proof.
  (* inv INIT. exploit Genv.find_funct_ptr_inversion; eauto. i. des. *)
  inv INIT. (* inv INIT0. *)
  assert (LOGICAL: forall b, m0.(Mem.mem_concrete) ! b = None).
  { i. eapply Genv.init_mem_logical; eauto. inv INIT0; eauto. }
  exploit nonempty_realloc_globals; eauto.
  { eapply Genv.find_funct_ptr_not_fresh; eauto. inv INIT0; eauto. }
  instantiate (1:=k). i. des.
  exploit find_instr_range_function; eauto.
Qed.

Lemma initial_state_r_permission2
    p rs m b ef k
    (INIT: initial_state_r p (State rs m))
    (FUNC: Genv.find_funct_ptr (Genv.globalenv p) b = Some (External ef)):
  Mem.perm m b 0 k Nonempty
/\ (forall ofs k p, Mem.perm m b ofs k p -> ofs = 0 /\ p = Nonempty).
Proof.
  inv INIT. inv INIT0. exploit Genv.init_mem_characterization_2; eauto.
  i. des. exploit nonempty_realloc_globals_external; eauto. i.
  unfold Mem.perm. erewrite <- H2. split; eauto. eapply Mem.perm_cur. eauto.
Qed.

Section FUNCPERM.

Variable p: program.  
Let ge := Genv.globalenv p.
Let sem := Asm.semantics p.

Definition mem_char (m: mem) :=
  forall b f, Genv.find_funct_ptr ge b = Some (Internal f) ->
  forall ofs i, find_instr ofs f.(fn_code) = Some i ->
  Mem.perm m b ofs Max Nonempty
  /\ (forall k p, Mem.perm m b ofs k p -> p = Nonempty).

Definition mem_char_ext (m: mem) :=
  forall b ef, Genv.find_funct_ptr ge b = Some (External ef) ->
  Mem.perm m b 0 Max Nonempty
  /\ (forall ofs k p, Mem.perm m b ofs k p -> ofs = 0 /\ p = Nonempty).

Definition mem_char_all (m: mem) := mem_char m /\ mem_char_ext m.

Definition state_char (s: state) : Prop :=
  mem_char_all (state_mem s).

Lemma initial_state_char
    s
    (INIT: initial_state_r p s):
  state_char s.
Proof.
  ii. dup INIT. inv INIT0. ss. r. r. splits; ss.
  - r. ii. eapply initial_state_r_permission1; eauto.
  - r. ii. eapply initial_state_r_permission2; eauto.
Qed.

Lemma store_mem_char
    chunk m b ofs v' m'
    (CHAR: mem_char m)
    (STORE: Mem.store chunk m b ofs v' = Some m'):
  mem_char m'.
Proof.
  r. i. exploit CHAR; eauto. i. des. split.
  { des_ifs; eapply Mem.perm_store_1; eauto. }
  i. des_ifs; eapply H2; eapply Mem.perm_store_2; eauto.
Qed.

Lemma store_mem_char_ext
    chunk m b ofs v' m'
    (CHAR: mem_char_ext m)
    (STORE: Mem.store chunk m b ofs v' = Some m'):
  mem_char_ext m'.
Proof.
  r. i. exploit CHAR; eauto. i. des. split.
  { des_ifs; eapply Mem.perm_store_1; eauto. }
  i. des_ifs; eapply H1; eapply Mem.perm_store_2; eauto.
Qed.

Lemma storev_mem_char
    chunk m v v' m'
    (CHAR: mem_char m)
    (STORE: Mem.storev chunk m v v' = Some m'):
  mem_char m'.
Proof.
  unfold Mem.storev in STORE. des_ifs; eapply store_mem_char; eauto.
Qed.

Lemma storev_mem_char_ext
    chunk m v v' m'
    (CHAR: mem_char_ext m)
    (STORE: Mem.storev chunk m v v' = Some m'):
  mem_char_ext m'.
Proof.
  unfold Mem.storev in STORE. des_ifs; eapply store_mem_char_ext; eauto.
Qed.

Lemma alloc_mem_char
    m lo hi m' b
    (CHAR: mem_char m)
    (ALLOC: Mem.alloc m lo hi = (m', b)):
  mem_char m'.
Proof.
  unfold mem_char in *. i. exploit CHAR; eauto. i. des.
  assert (b0 <> b).
  { hexploit Mem.fresh_block_alloc; eauto. i.
    eapply Mem.perm_valid_block in H1. ii; subst; clarify. }
  split; [eapply Mem.perm_alloc_1; eauto|].
  i. eapply H2. eapply Mem.perm_alloc_4; eauto.
Qed.

Lemma alloc_mem_char_ext
    m lo hi m' b
    (CHAR: mem_char_ext m)
    (ALLOC: Mem.alloc m lo hi = (m', b)):
  mem_char_ext m'.
Proof.
  unfold mem_char_ext in *. i. exploit CHAR; eauto. i. des.
  assert (b0 <> b).
  { hexploit Mem.fresh_block_alloc; eauto. i.
    eapply Mem.perm_valid_block in H0. ii; subst; clarify. }
  split; [eapply Mem.perm_alloc_1; eauto|].
  i. eapply H1. eapply Mem.perm_alloc_4; eauto.
Qed.

Lemma free_mem_char
    m b hi m'
    (CHAR: mem_char m)
    (FREE: Mem.free m b 0 hi = Some m'):
  mem_char m'.
Proof.
  r. i. exploit CHAR; eauto. i. des. split.
  2:{ i. eapply H2. eapply Mem.perm_free_3; eauto. }
  hexploit Mem.free_range_perm; eauto. intros FPERM.
  destruct (classic (hi > ofs)); cycle 1.
  { eapply Mem.perm_free_1; eauto. }
  destruct (peq b0 b); cycle 1.
  { eapply Mem.perm_free_1; eauto. }
  subst. specialize (FPERM ofs). exploit FPERM; try lia.
  { eapply find_instr_range_function in H0. lia. }
  i. eapply H2 in H4. des; clarify.
Qed.

Lemma free_mem_char_ext
    m b hi m'
    (CHAR: mem_char_ext m)
    (FREE: Mem.free m b 0 hi = Some m'):
  mem_char_ext m'.
Proof.
  r. i. exploit CHAR; eauto. i. des. split.
  2:{ i. eapply H1. eapply Mem.perm_free_3; eauto. }
  hexploit Mem.free_range_perm; eauto. intros FPERM.
  destruct (classic (hi > 0)); cycle 1.
  { eapply Mem.perm_free_1; eauto. }
  destruct (peq b0 b); cycle 1.
  { eapply Mem.perm_free_1; eauto. }
  subst. specialize (FPERM 0). exploit FPERM; try lia. i.
  eapply H1 in H3. des; clarify.
Qed.

Lemma store_mem_char_all
    chunk m b ofs v' m'
    (CHAR: mem_char_all m)
    (STORE: Mem.store chunk m b ofs v' = Some m'):
  mem_char_all m'.
Proof.
  inv CHAR. r.
  eapply store_mem_char in H; eauto. eapply store_mem_char_ext in H0; eauto.
Qed.

Lemma storev_mem_char_all
    chunk m v v' m'
    (CHAR: mem_char_all m)
    (STORE: Mem.storev chunk m v v' = Some m'):
  mem_char_all m'.
Proof.
  unfold Mem.storev in STORE. des_ifs; eapply store_mem_char_all; eauto.
Qed.

Lemma alloc_mem_char_all
    m lo hi m' b
    (CHAR: mem_char_all m)
    (ALLOC: Mem.alloc m lo hi = (m', b)):
  mem_char_all m'.
Proof.
  inv CHAR. r.
  eapply alloc_mem_char in H; eauto. eapply alloc_mem_char_ext in H0; eauto.
Qed.

Lemma free_mem_char_all
    m b hi m'
    (CHAR: mem_char_all m)
    (FREE: Mem.free m b 0 hi = Some m'):
  mem_char_all m'.
Proof.
  inv CHAR. r.
  eapply free_mem_char in H; eauto. eapply free_mem_char_ext in H0; eauto.
Qed.

Lemma state_char_preservation_astep
    s s' tr
    (CHAR: state_char s)
    (STEP: astep ge s tr s'):
  state_char s'.
Proof.
  Local Transparent Mem.free.
  inv STEP; ss; unfold state_char in *; ss.
  - destruct i; ss; clarify; eauto; try by (unfold exec_load in *; des_ifs).
    + unfold exec_store in *. des_ifs. eapply storev_mem_char_all; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char_all; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char_all; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char_all; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char_all; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char_all; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char_all; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char_all; eauto.
    + unfold goto_label in H2. des_ifs.
    + unfold goto_label in H2. des_ifs.
    + unfold goto_label in H2. des_ifs.
    + unfold goto_label in H2. des_ifs.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char_all; eauto.
    + unfold exec_store in *. des_ifs. eapply storev_mem_char_all; eauto.
    + des_ifs.
      eapply store_mem_char_all; try eapply Heq1.
      eapply store_mem_char_all; try eapply Heq0.
      eapply alloc_mem_char_all; eauto.
    + des_ifs. eapply free_mem_char_all; eauto.
  - r. destruct CHAR as [CHAR1 CHAR2]. i. split.
    + ii. exploit CHAR1; eauto. i. des. split; cycle 1.
      { i. eapply H7. instantiate (1:=Max).
        eapply external_call_max_perm; eauto.
        { eapply Mem.perm_valid_block; eauto. }
        eapply Mem.perm_max; eauto. }
      assert (NM: nonempty_perm m b0 ofs0).
      { r. split; eauto. }
      exploit ec_nonempty; eauto.
      { eapply external_call_common_spec. }
      i. r in H8. des; eauto.
    + ii. exploit CHAR2; eauto. i. des. split; cycle 1.
      { i. eapply H6. instantiate (1:=Max).
        eapply external_call_max_perm; eauto.
        { eapply Mem.perm_valid_block; eauto. }
        eapply Mem.perm_max; eauto. }
      assert (NM: nonempty_perm m b0 0).
      { r. split; eauto. i. exploit H6; eauto. i. des; eauto. }
      exploit ec_nonempty; eauto.
      { eapply external_call_common_spec. }
      i. r in H7. des; eauto.
  - r. destruct CHAR as [CHAR1 CHAR2]. split.
    + ii. exploit CHAR1; eauto. i. des. split; cycle 1.
      { i. eapply H6. instantiate (1:=Max).
        eapply external_call_max_perm; eauto.
        { eapply Mem.perm_valid_block; eauto. }
        eapply Mem.perm_max; eauto. }
      assert (NM: nonempty_perm m b0 ofs).
      { r. split; eauto. }
      exploit ec_nonempty; eauto.
      { eapply external_call_common_spec. }
      i. r in H7. des; eauto.
    + ii. exploit CHAR2; eauto. i. des. split; cycle 1.
      { i. eapply H5. instantiate (1:=Max).
        eapply external_call_max_perm; eauto.
        { eapply Mem.perm_valid_block; eauto. }
        eapply Mem.perm_max; eauto. }
      assert (NM: nonempty_perm m b0 0).
      { r. split; eauto. i. exploit H5; eauto. i. des; eauto. }
      exploit ec_nonempty; eauto.
      { eapply external_call_common_spec. }
      i. r in H6. des; eauto.
Qed.

Lemma state_char_preservation_cstep
    s s'
    (CHAR: state_char s)
    (STEP: cstep s s'):
  state_char s'.
Proof.
  inv STEP. r in CONC. r in CCONC. des.
  assert (SAMEACC: Mem.mem_access m = Mem.mem_access m'').
  { rewrite CONC0. eauto. }
  unfold state_char in *. ss. inv CHAR. split.
  - unfold mem_char in *. unfold Mem.perm. rewrite <- SAMEACC. eauto.
  - unfold mem_char_ext in *. unfold Mem.perm. rewrite <- SAMEACC. eauto.
Qed.

Lemma state_char_preservation
    s s' tr
    (CHAR: state_char s)
    (STEP: step ge s tr s'):
  state_char s'.
Proof.
  inv STEP.
  - eapply state_char_preservation_cstep; try eapply CSTEP.
    eapply state_char_preservation_astep; eauto.
  - eapply state_char_preservation_astep; eauto.
Qed.

Lemma state_char_star
    s s' tr
    (CHAR: state_char s)
    (STEP: star step ge s tr s'):
  state_char s'.
Proof.
  ginduction STEP; eauto. i. eapply IHSTEP. eapply state_char_preservation; eauto.
Qed.

Lemma state_char_plus
    s s' tr
    (CHAR: state_char s)
    (STEP: plus step ge s tr s'):
  state_char s'.
Proof.
  inv STEP. eapply state_char_star; try eapply H0; eauto. eapply state_char_preservation; eauto.
Qed.

End FUNCPERM.
  
(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2).
  { intros. inv H; inv H0; congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2).
  { intros. inv H; inv H0.
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | PC => false
  | IR _ => true
  | FR _ => true
  | ST0 => true
  | CR _ => false
  | RA => false
  end.

Require Import Asm.

Section PRESERVATION.

Definition rs_binded (m: mem) (rs rs': regset) : Prop :=
  forall r, val_intptr m (rs#r) (rs'#r).

Lemma rs_binded_refl m rs: rs_binded m rs rs.
Proof. ii. eapply val_intptr_refl. Qed.

Variable prog: Asm.program.
(* Hypothesis TRANSF: match_prog prog tprog. *)
Let ge := Genv.globalenv prog.
(* Let tge := Genv.globalenv tprog. *)

Let sem := Asm.semantics prog.
Let tsem := Lowerbound.semantics prog.

Variables st_init_tgt (* st_init_tgt0 *) st_init_tgt1: tsem.(Smallstep.state).
Hypothesis INIT1: tsem.(Smallstep.initial_state) st_init_tgt.
(* Hypothesis ICAP0: Lowerbound.glob_capture prog st_init_tgt st_init_tgt0. *)
Hypothesis ICAP1: tsem.(Smallstep.initial_capture) st_init_tgt st_init_tgt1.
Definition gmtgt : ident -> option Z := tsem.(initial_pimap) st_init_tgt1.

Inductive match_states: Asm.state -> Lowerbound.state -> Prop :=
| match_states_intro
    rs rs' m m'
    (MCEXT: concrete_extends m m')
    (RCEXT: rs_binded m' rs rs'):
  match_states (Asm.State rs m) (Lowerbound.State rs' m').

Lemma pc_add_one_bind
    m v1 v2
    (VBIND: val_intptr m v1 v2):
  val_intptr m (Val.offset_ptr v1 Ptrofs.one) (val_add_one v2).
Proof.
  inv VBIND; ss; try by econs. des_ifs. econs; eauto.
  ss. unfold Mem.ptr2int in *. des_ifs_safe.
  do 2 f_equal. unfold Int64.add. eapply Int64.same_if_eq. unfold Int64.eq.
  des_ifs. exfalso. eapply n. unfold Ptrofs.add.
  repeat rewrite Int64.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
  rewrite Int64.unsigned_one. rewrite Ptrofs.unsigned_one. rewrite Ptrofs.modulus_eq64; eauto.
  rewrite Zplus_mod_idemp_r. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma pc_add_delta_bind
    m v1 v2 delta
    (VBIND: val_intptr m v1 v2):
  val_intptr m (Val.offset_ptr v1 delta) (val_add_ptrofs v2 delta).
Proof.
  inv VBIND; ss; try by econs. des_ifs. econs; eauto.
  ss. unfold Mem.ptr2int in *. des_ifs_safe.
  do 2 f_equal. unfold Int64.add. eapply Int64.same_if_eq. unfold Int64.eq.
  des_ifs. exfalso. eapply n. unfold Ptrofs.add. unfold Ptrofs.to_int64.
  repeat rewrite Int64.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
  rewrite Ptrofs.modulus_eq64; eauto.
  repeat rewrite Zplus_mod_idemp_r. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma set_bind
    m rs1 rs2 rd v1 v2
    (VBIND: val_intptr m v1 v2)
    (RCEXT : rs_binded m rs1 rs2):
  rs_binded m (rs1 # rd <- v1) (rs2 # rd <- v2).
Proof.
  ii. destruct (classic (r = rd)); subst.
  { do 2 (erewrite Pregmap.gss; eauto). }
  do 2 (erewrite Pregmap.gso; eauto).
Qed.
  
Lemma nextinstr_sim
    m rs1 rs2 (RCEXT : rs_binded m rs1 rs2):
  rs_binded m (Asm.nextinstr rs1) (Lowerbound.nextinstr rs2).
Proof.
  r. i. unfold Asm.nextinstr, Lowerbound.nextinstr. eapply set_bind; eauto.
  eapply pc_add_one_bind; eauto.
Qed.

Lemma nextinstr_nf_sim
    m rs1 rs2 (RCEXT : rs_binded m rs1 rs2):
  rs_binded m (Asm.nextinstr_nf rs1) (Lowerbound.nextinstr_nf rs2).
Proof.
  r. i. unfold Asm.nextinstr_nf, Lowerbound.nextinstr_nf. eapply set_bind; eauto.
  { eapply pc_add_one_bind; eauto. ss. repeat (eapply set_bind; eauto); econs. }
  repeat (eapply set_bind; eauto); econs.
Qed.

Lemma addrmode64_bind
    m rs1 rs2 a (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (eval_addrmode64 ge a rs1) (eval_addrmode64 ge a rs2).
Proof.
  destruct a; ss. eapply addl_bind.
  { des_ifs. eapply val_intptr_refl. }
  eapply addl_bind.
  { des_ifs; cycle 1.
    - eapply val_intptr_refl.
    - eapply mull_bind; eauto. econs. }
  des_ifs; eapply val_intptr_refl.
Qed.

Lemma addrmode32_bind
    m rs1 rs2 a (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (eval_addrmode32 ge a rs1) (eval_addrmode32 ge a rs2).
Proof.
  destruct a; ss. eapply add_bind.
  { des_ifs. eapply val_intptr_refl. }
  eapply add_bind.
  { des_ifs; cycle 1.
    - eapply val_intptr_refl.
    - eapply mul_bind; eauto. econs. }
  des_ifs; eapply val_intptr_refl.
Qed.

Lemma addrmode_bind
    m rs1 rs2 a (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (eval_addrmode ge a rs1) (eval_addrmode ge a rs2).
Proof.
  unfold eval_addrmode. destruct Archi.ptr64.
  - eapply addrmode64_bind; eauto.
  - eapply addrmode32_bind; eauto.
Qed.

Lemma exec_load_fsim
    chunk a rd rs1 rs2 m1 m2 rs1' m1'
    (EXEC : exec_load ge chunk m1 a rs1 rd = Next rs1' m1')
    (MCEXT : concrete_extends m1 m2)
    (RCEXT : rs_binded m2 rs1 rs2):
  exists rs2' m2',
    Lowerbound.exec_load ge chunk m2 a rs2 rd = Next rs2' m2'
  /\ concrete_extends m1' m2'
  /\ rs_binded m2' rs1' rs2'.
Proof.
  unfold exec_load in EXEC. des_ifs.
  exploit loadv_concrete_extends; eauto.
  { eapply addrmode_bind; eauto. }
  i. des. esplits; eauto.
  { unfold Lowerbound.exec_load. rewrite H. esplits; eauto. }
  eapply nextinstr_nf_sim. eapply set_bind; eauto.
Qed.

Lemma undef_regs_binded
    m rs1 rs2 dr
    (RCEXT: rs_binded m rs1 rs2):
  rs_binded m (undef_regs dr rs1) (undef_regs dr rs2).
Proof.
  revert RCEXT. revert rs1 rs2.
  induction dr; ss; i. eapply IHdr. eapply set_bind; eauto. econs.
Qed.

Lemma same_concrete_rs_bind
    m m' rs1 rs2
    (SAME: m.(Mem.mem_concrete) = m'.(Mem.mem_concrete)):
  rs_binded m rs1 rs2 <-> rs_binded m' rs1 rs2.
Proof.
  split; ii.
  - eapply same_conc_val_intptr; eauto.
  - symmetry in SAME. eapply same_conc_val_intptr; eauto.
Qed.

Lemma exec_store_fsim
    chunk a rs1 rs2 m1 m2 r dr rs1' m1'
    (EXEC : exec_store ge chunk m1 a rs1 r dr = Next rs1' m1')
    (MCEXT : concrete_extends m1 m2)
    (RCEXT : rs_binded m2 rs1 rs2):
  exists rs2' m2',
    Lowerbound.exec_store ge chunk m2 a rs2 r dr = Next rs2' m2'
  /\ concrete_extends m1' m2'
  /\ rs_binded m2' rs1' rs2'.
Proof.
  unfold exec_store in EXEC. des_ifs.
  exploit storev_concrete_extends; eauto.
  { eapply addrmode_bind; eauto. }
  i. des. esplits; eauto.
  { unfold Lowerbound.exec_store. rewrite H. esplits; eauto. }
  eapply nextinstr_nf_sim. 
  eapply undef_regs_binded. erewrite <- same_concrete_rs_bind; eauto.
  eapply Mem.storev_concrete; eauto.
Qed.

Lemma zero_ext_bind
    m rs1 rs2 n rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.zero_ext n (rs1 rs)) (Val.zero_ext n (rs2 rs)).
Proof.
  unfold Val.zero_ext. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
Qed.

Lemma sign_ext_bind
    m rs1 rs2 n rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.sign_ext n (rs1 rs)) (Val.sign_ext n (rs2 rs)).
Proof.
  unfold Val.sign_ext. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
Qed.

Lemma longofintu_bind
    m rs1 rs2 rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.longofintu (rs1 rs)) (Val.longofintu (rs2 rs)).
Proof.
  unfold Val.longofintu. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
Qed.

Lemma longofint_bind
    m rs1 rs2 rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.longofint (rs1 rs)) (Val.longofint (rs2 rs)).
Proof.
  unfold Val.longofint. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
Qed.

Lemma loword_bind
    m rs1 rs2 rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.loword (rs1 rs)) (Val.loword (rs2 rs)).
Proof.
  unfold Val.loword. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
Qed.

Lemma singleoffloat_bind
    m rs1 rs2 rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.singleoffloat (rs1 rs)) (Val.singleoffloat (rs2 rs)).
Proof.
  unfold Val.singleoffloat. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
Qed.

Lemma floatofsingle_bind
    m rs1 rs2 rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.floatofsingle (rs1 rs)) (Val.floatofsingle (rs2 rs)).
Proof.
  unfold Val.floatofsingle. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
Qed.

Lemma intoffloat_bind
    m rs1 rs2 rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.maketotal (Val.intoffloat (rs1 rs))) (Val.maketotal (Val.intoffloat (rs2 rs))).
Proof.
  unfold Val.intoffloat. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
  unfold option_map. des_ifs; ss; econs.
Qed.

Lemma floatofint_bind
    m rs1 rs2 rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.maketotal (Val.floatofint (rs1 rs))) (Val.maketotal (Val.floatofint (rs2 rs))).
Proof.
  unfold Val.floatofint. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
Qed.

Lemma intofsingle_bind
    m rs1 rs2 rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.maketotal (Val.intofsingle (rs1 rs))) (Val.maketotal (Val.intofsingle (rs2 rs))).
Proof.
  unfold Val.intofsingle. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
  unfold option_map. des_ifs; ss; econs.
Qed.

Lemma singleofint_bind
    m rs1 rs2 rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.maketotal (Val.singleofint (rs1 rs))) (Val.maketotal (Val.singleofint (rs2 rs))).
Proof.
  unfold Val.singleofint. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
Qed.

Lemma longoffloat_bind
    m rs1 rs2 rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.maketotal (Val.longoffloat (rs1 rs))) (Val.maketotal (Val.longoffloat (rs2 rs))).
Proof.
  unfold Val.longoffloat. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
  unfold option_map. des_ifs; ss; econs.
Qed.

Lemma floatoflong_bind
    m rs1 rs2 rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.maketotal (Val.floatoflong (rs1 rs))) (Val.maketotal (Val.floatoflong (rs2 rs))).
Proof.
  unfold Val.floatoflong. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
Qed.

Lemma longofsingle_bind
    m rs1 rs2 rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.maketotal (Val.longofsingle (rs1 rs))) (Val.maketotal (Val.longofsingle (rs2 rs))).
Proof.
  unfold Val.longofsingle. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
  unfold option_map. des_ifs; ss; econs.
Qed.

Lemma singleoflong_bind
    m rs1 rs2 rs
    (RCEXT : rs_binded m rs1 rs2):
  val_intptr m (Val.maketotal (Val.singleoflong (rs1 rs))) (Val.maketotal (Val.singleoflong (rs2 rs))).
Proof.
  unfold Val.singleoflong. specialize (RCEXT rs). des_ifs; inv RCEXT; try econs.
Qed.

Lemma and_bind
    m v1 v2 v1' v2'
    (RCEXT: val_intptr m v1 v1')
    (RCEXT0: val_intptr m v2 v2'):
  val_intptr m (Val.and v1 v2) (Val.and v1' v2').
Proof.
  destruct v1, v2; ss; inv RCEXT; inv RCEXT0; ss; try econs.
Qed.

Lemma andl_bind
    m v1 v2 v1' v2'
    (RCEXT: val_intptr m v1 v1')
    (RCEXT0: val_intptr m v2 v2'):
  val_intptr m (Val.andl v1 v2) (Val.andl v1' v2').
Proof.
  destruct v1, v2; ss; inv RCEXT; inv RCEXT0; ss; try econs.
Qed.

Lemma hiword_bind
    m v v'
    (BIND: val_intptr m v v'):
  val_intptr m (Val.hiword v) (Val.hiword v').
Proof. inv BIND; ss; try econs. Qed.

Lemma loword_bind'
    m v v'
    (BIND: val_intptr m v v'):
  val_intptr m (Val.loword v) (Val.loword v').
Proof. inv BIND; ss; try econs. Qed.

Lemma longofwords_bind
    m v1 v2 v1' v2'
    (BIND1: val_intptr m v1 v1')
    (BIND2: val_intptr m v2 v2'):
  val_intptr m (Val.longofwords v1 v2) (Val.longofwords v1' v2').
Proof. inv BIND1; inv BIND2; econs. Qed.

Lemma set_res_bind
    m bres v v' rs rs'
    (BIND: val_intptr m v v')
    (RCEXT: rs_binded m rs rs'):
  rs_binded m (set_res bres v rs) (set_res bres v' rs').
Proof.
  revert RCEXT BIND. revert rs rs' v v' m. induction bres; ss; i.
  - eapply set_bind; eauto.
  - eapply IHbres2.
    + eapply IHbres1; eauto. eapply hiword_bind. eauto.
    + eapply loword_bind'. eauto.
Qed.

Lemma set_pair_bind
    m bres v v' rs rs'
    (BIND: val_intptr m v v')
    (RCEXT: rs_binded m rs rs'):
  rs_binded m (set_pair bres v rs) (set_pair bres v' rs').
Proof.
  destruct bres; ss.
  { eapply set_bind; eauto. }
  eapply set_bind; eauto.
  - eapply loword_bind'; eauto.
  - eapply set_bind; eauto. eapply hiword_bind. eauto.
Qed.

Lemma eval_testcond_bind
    c m rs1 rs2 b
    (RCEXT: rs_binded m rs1 rs2)
    (TEST: eval_testcond c rs1 = Some b):
  eval_testcond c rs2 = Some b.
Proof.
  unfold eval_testcond in TEST. des_ifs; ss.
  - specialize (RCEXT ZF). rewrite Heq in RCEXT. inv RCEXT. ss.
  - specialize (RCEXT ZF). rewrite Heq in RCEXT. inv RCEXT. ss.
  - specialize (RCEXT CF). rewrite Heq in RCEXT. inv RCEXT. ss.
  - dup RCEXT. specialize (RCEXT CF). specialize (RCEXT0 ZF).
    rewrite Heq in RCEXT. rewrite Heq0 in RCEXT0. inv RCEXT; inv RCEXT0; ss.
  - specialize (RCEXT CF). rewrite Heq in RCEXT. inv RCEXT. ss.
  - dup RCEXT. specialize (RCEXT CF). specialize (RCEXT0 ZF).
    rewrite Heq in RCEXT. rewrite Heq0 in RCEXT0. inv RCEXT; inv RCEXT0; ss.
  - dup RCEXT. specialize (RCEXT OF). specialize (RCEXT0 SF).
    rewrite Heq in RCEXT. rewrite Heq0 in RCEXT0. inv RCEXT; inv RCEXT0; ss.
  - dup RCEXT. dup RCEXT0. specialize (RCEXT OF). specialize (RCEXT0 SF). specialize (RCEXT1 ZF).
    rewrite Heq in RCEXT. rewrite Heq0 in RCEXT0. rewrite Heq1 in RCEXT1.
    inv RCEXT; inv RCEXT0; inv RCEXT1; ss.
  - dup RCEXT. specialize (RCEXT OF). specialize (RCEXT0 SF).
    rewrite Heq in RCEXT. rewrite Heq0 in RCEXT0. inv RCEXT; inv RCEXT0; ss.
  - dup RCEXT. dup RCEXT0. specialize (RCEXT OF). specialize (RCEXT0 SF). specialize (RCEXT1 ZF).
    rewrite Heq in RCEXT. rewrite Heq0 in RCEXT0. rewrite Heq1 in RCEXT1.
    inv RCEXT; inv RCEXT0; inv RCEXT1; ss.
  - specialize (RCEXT PF). rewrite Heq in RCEXT. inv RCEXT. ss.
  - specialize (RCEXT PF). rewrite Heq in RCEXT. inv RCEXT. ss.
Qed.

Lemma psubl_join_asm_psub_join
    m v1 v2
    (SF: Archi.ptr64 = true)
    (NOTALLPTR: forall b1 ofs1 b2 ofs2, ~ (v1 = Vptr b1 ofs1 /\ v2 = Vptr b2 ofs2)):
  psub_join_asm m v1 v2 = psubl_join m v1 v2.
Proof.
  destruct v1, v2; ss;
    (try by (unfold psub_join_asm, psubl_join; ss; unfold to_ptr_val; ss; des_ifs));
    (try by (unfold psub_join_asm, psubl_join; ss; unfold to_int_val; ss; des_ifs)).
  - unfold psub_join_asm, psubl_join. erewrite val_join_angelic_vi; try by ss.
    eapply psubl_wrapper_no_angelic; eauto.
  - exfalso. eapply NOTALLPTR; eauto.
Qed.
    

Lemma psub_join_asm_bind
    m1 m2 v1 v1' v2 v2'
    (RCEXT: val_intptr m2 v1 v1')
    (RCEXT0: val_intptr m2 v2 v2')
    (MCEXT: concrete_extends m1 m2):
  val_intptr m2 (psub_join_asm m1 v1 v2) (psub_join_asm m2 v1' v2').
Proof.
  (* unfold psub_join_asm. des_ifs_safe. *)
  exploit psubl_join_binded. eauto. eapply RCEXT. eapply RCEXT0. eauto. i. des. subst.
  rename BIND into PSUBL.
  destruct v1, v2; try by (ss; des_ifs; econs).
  - inv RCEXT; inv RCEXT0; try by (ss; des_ifs; econs).
  - inv RCEXT; inv RCEXT0; try by (ss; des_ifs; econs).
    + do 2 try (erewrite psubl_join_asm_psub_join; eauto).
      { ii. des; clarify. }
      { ii. des; clarify. }
  - inv RCEXT; inv RCEXT0; try by (ss; des_ifs; econs).
    do 2 try (erewrite psubl_join_asm_psub_join; eauto).
    { ii. des; clarify. }
    { ii. des; clarify. }
  - unfold psub_join_asm, psubl_join_common at 1. des_ifs.
    destruct (classic ((Val.psubl (Vptr b i) (Vptr b0 i0)) = Vundef)).
    { rewrite H. econs. }
    dup RCEXT. dup RCEXT0.
    exploit psubl_join_binded. eauto. eapply RCEXT. eapply RCEXT0.
    { instantiate (1:= Val.psubl (Vptr b i) (Vptr b0 i0)). unfold psubl_join. rewrite val_join_angelic_vp.
      - simpl. eauto.
      - ss. des_ifs.
      - eapply psubl_wrapper_no_angelic; eauto.
      - ii. ss. }
    i. des. inv RCEXT; inv RCEXT0; ss.
    { des_ifs_safe. unfold psub_join_asm. ss. des_ifs_safe. eapply val_intptr_refl. }
    { unfold psub_join_asm. ss. des_ifs_safe. unfold psubl_join in BIND.
      rewrite val_join_angelic_vi in BIND; eauto; [|ss].
      eapply psubl_wrapper_no_angelic; eauto. }
Qed.

Lemma cmplu_join_asm_bind
    c m1 m2 v1 v1' v2 v2' v
    (RCEXT: val_intptr m2 v1 v1')
    (RCEXT0: val_intptr m2 v2 v2')
    (MCEXT: concrete_extends m1 m2)
    (CMP: cmplu_join_asm m1 c v1 v2 = Some v):
  exists v', cmplu_join_asm m2 c v1' v2' = Some v'
      /\ val_intptr m2 v v'.
Proof.
  unfold cmplu_join_asm in *. erewrite cmplu_join_same_eval_condition_join in *.
  destruct (eval_condition_join (Op.Ccomplu c) [v1; v2] m1) eqn: CMP1; try by ss.
  exploit eval_condition_join_binded; eauto; [ss| |].
  { econs; eauto. econs; eauto. econs. }
  i. erewrite H. esplits; eauto. eapply val_intptr_refl.
Qed.

Lemma compare_longs_binded
    m1 m2 v1 v1' v2 v2' rs1 rs2
    (BIND1: val_intptr m2 v1 v1')
    (BIND2: val_intptr m2 v2 v2')
    (MCEXT: concrete_extends m1 m2)
    (RCEXT: rs_binded m2 rs1 rs2):
  rs_binded m2 (compare_longs v1 v2 rs1 m1) (compare_longs v1' v2' rs2 m2).
Proof.
  ii. unfold compare_longs. eapply set_bind.
  { econs. }
  eapply set_bind.
  { destruct v1, v2; ss; try econs. inv BIND1; inv BIND2; ss. eapply val_intptr_refl. }
  eapply set_bind.
  { exploit subl_bind. eapply BIND1. eapply BIND2. i. inv H; ss; try by econs. }
  eapply set_bind.
  { destruct (cmplu_join_asm m1 Clt v1 v2) eqn:CMP; try by econs.
    eapply cmplu_join_asm_bind in CMP; eauto. des. erewrite CMP. ss. }
  eapply set_bind; eauto.
  { destruct (cmplu_join_asm m1 Ceq v1 v2) eqn:CMP; try by econs.
    eapply cmplu_join_asm_bind in CMP; eauto. des. erewrite CMP. ss. }
Qed.

Lemma compare_ints_binded
    m1 m2 v1 v1' v2 v2' rs1 rs2
    (BIND1: val_intptr m2 v1 v1')
    (BIND2: val_intptr m2 v2 v2')
    (MCEXT: concrete_extends m1 m2)
    (RCEXT: rs_binded m2 rs1 rs2):
  rs_binded m2 (compare_ints v1 v2 rs1 m1) (compare_ints v1' v2' rs2 m2).
Proof.
  ii. unfold compare_ints. eapply set_bind.
  { econs. }
  eapply set_bind.
  { destruct v1, v2; ss; try econs. inv BIND1; inv BIND2; ss. eapply val_intptr_refl. }
  eapply set_bind.
  { exploit sub_bind. eapply BIND1. eapply BIND2. i. inv H; ss; try by econs. }
  eapply set_bind.
  { inv BIND1; inv BIND2; ss; (try by eapply val_intptr_refl); unfold Val.cmpu; ss; try by econs. }
  eapply set_bind; eauto.
  { inv BIND1; inv BIND2; ss; (try by eapply val_intptr_refl); unfold Val.cmpu; ss; try by econs. }
Qed.

Lemma addf_bind
    m v1 v2 v1' v2'
    (BIND1: val_intptr m v1 v1')
    (BIND2: val_intptr m v2 v2'):
  val_intptr m (Val.addf v1 v2) (Val.addf v1' v2').
Proof. inv BIND1; inv BIND2; econs. Qed.

Lemma subf_bind
    m v1 v2 v1' v2'
    (BIND1: val_intptr m v1 v1')
    (BIND2: val_intptr m v2 v2'):
  val_intptr m (Val.subf v1 v2) (Val.subf v1' v2').
Proof. inv BIND1; inv BIND2; econs. Qed.

Lemma mulf_bind
    m v1 v2 v1' v2'
    (BIND1: val_intptr m v1 v1')
    (BIND2: val_intptr m v2 v2'):
  val_intptr m (Val.mulf v1 v2) (Val.mulf v1' v2').
Proof. inv BIND1; inv BIND2; econs. Qed.

Lemma divf_bind
    m v1 v2 v1' v2'
    (BIND1: val_intptr m v1 v1')
    (BIND2: val_intptr m v2 v2'):
  val_intptr m (Val.divf v1 v2) (Val.divf v1' v2').
Proof. inv BIND1; inv BIND2; econs. Qed.

Lemma negf_bind
    m v v'
    (BIND1: val_intptr m v v'):
  val_intptr m (Val.negf v) (Val.negf v').
Proof. inv BIND1; econs. Qed.

Lemma absf_bind
    m v v'
    (BIND1: val_intptr m v v'):
  val_intptr m (Val.absf v) (Val.absf v').
Proof. inv BIND1; econs. Qed.

Lemma compare_floats_binded
    m1 m2 v1 v1' v2 v2' rs1 rs2
    (BIND1: val_intptr m2 v1 v1')
    (BIND2: val_intptr m2 v2 v2')
    (MCEXT: concrete_extends m1 m2)
    (RCEXT: rs_binded m2 rs1 rs2):
  rs_binded m2 (compare_floats v1 v2 rs1) (compare_floats v1' v2' rs2).
Proof.
  ii. unfold compare_floats. inv BIND1; inv BIND2; (try by (eapply undef_regs_binded; eauto));
    (des_ifs; try by  (eapply undef_regs_binded; eauto)).
  - eapply set_bind; try econs. eapply set_bind; try econs. eapply set_bind.
    { eapply val_intptr_refl. }
    eapply set_bind.
    { eapply val_intptr_refl. }
    eapply set_bind; eauto.
    { eapply val_intptr_refl. }
  - eapply set_bind; try econs. eapply set_bind; try econs. eapply set_bind.
    { econs. }
    eapply set_bind.
    { econs. }
    eapply set_bind; eauto. econs.
  - repeat (eapply set_bind; [econs|]). eauto.
  - repeat (eapply set_bind; [econs|]). eauto.
Qed.
  
Lemma addfs_bind
    m v1 v2 v1' v2'
    (BIND1: val_intptr m v1 v1')
    (BIND2: val_intptr m v2 v2'):
  val_intptr m (Val.addfs v1 v2) (Val.addfs v1' v2').
Proof. inv BIND1; inv BIND2; econs. Qed.

Lemma subfs_bind
    m v1 v2 v1' v2'
    (BIND1: val_intptr m v1 v1')
    (BIND2: val_intptr m v2 v2'):
  val_intptr m (Val.subfs v1 v2) (Val.subfs v1' v2').
Proof. inv BIND1; inv BIND2; econs. Qed.

Lemma mulfs_bind
    m v1 v2 v1' v2'
    (BIND1: val_intptr m v1 v1')
    (BIND2: val_intptr m v2 v2'):
  val_intptr m (Val.mulfs v1 v2) (Val.mulfs v1' v2').
Proof. inv BIND1; inv BIND2; econs. Qed.

Lemma divfs_bind
    m v1 v2 v1' v2'
    (BIND1: val_intptr m v1 v1')
    (BIND2: val_intptr m v2 v2'):
  val_intptr m (Val.divfs v1 v2) (Val.divfs v1' v2').
Proof. inv BIND1; inv BIND2; econs. Qed.

Lemma negfs_bind
    m v v'
    (BIND1: val_intptr m v v'):
  val_intptr m (Val.negfs v) (Val.negfs v').
Proof. inv BIND1; econs. Qed.

Lemma absfs_bind
    m v v'
    (BIND1: val_intptr m v v'):
  val_intptr m (Val.absfs v) (Val.absfs v').
Proof. inv BIND1; econs. Qed.

Lemma compare_floats32_binded
    m1 m2 v1 v1' v2 v2' rs1 rs2
    (BIND1: val_intptr m2 v1 v1')
    (BIND2: val_intptr m2 v2 v2')
    (MCEXT: concrete_extends m1 m2)
    (RCEXT: rs_binded m2 rs1 rs2):
  rs_binded m2 (compare_floats32 v1 v2 rs1) (compare_floats32 v1' v2' rs2).
Proof.
  ii. unfold compare_floats. inv BIND1; inv BIND2; (try by (eapply undef_regs_binded; eauto));
    (des_ifs; try by  (eapply undef_regs_binded; eauto)); ss.
  - eapply set_bind; try econs. eapply set_bind; try econs. eapply set_bind.
    { eapply val_intptr_refl. }
    eapply set_bind.
    { eapply val_intptr_refl. }
    eapply set_bind; eauto.
    { eapply val_intptr_refl. }
  - des_ifs; try repeat (eapply set_bind; [econs|]); eauto.
  - destruct v1'; ss; repeat (eapply set_bind; [econs|]); eauto.
  - destruct v1'; ss; repeat (eapply set_bind; [econs|]); eauto.
  - destruct v1'; ss; repeat (eapply set_bind; [econs|]); eauto.
  - destruct v1'; ss; repeat (eapply set_bind; [econs|]); eauto.
  - destruct v1'; ss; repeat (eapply set_bind; [econs|]); eauto.
  - destruct v1'; ss; repeat (eapply set_bind; [econs|]); eauto.
  - destruct v1', v2'; ss; repeat (eapply set_bind; [econs|]); eauto.
Qed.

Lemma internal_pc_fsim
    b ofs f i m rs rs'
    (MCHAR: mem_char_all prog m)
    (SPC: rs PC = Vptr b ofs)
    (INT: Genv.find_funct_ptr ge b = Some (Internal f))
    (FIND: find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i)
    (RCEXT : rs_binded m rs rs'):
  Mem.to_ptr (rs' PC) m = Some (Vptr b ofs).
Proof.
  inv MCHAR. r in H. exploit H; eauto. i. des.
  dup RCEXT. specialize (RCEXT0 PC). rewrite SPC in RCEXT0. inv RCEXT0; ss.
  des_ifs_safe. exploit Mem.ptr2int_to_denormalize_max; eauto.
  { eapply Ptrofs.unsigned_range_2. }
  i. des. exploit Mem.denormalize_info; eauto. i. des.
  erewrite Int64.unsigned_repr.
  2:{ unfold Int64.max_unsigned, Ptrofs.max_unsigned in *. erewrite <- Ptrofs.modulus_eq64; eauto. lia. }
  des_ifs.
  2:{ rewrite Ptrofs.repr_unsigned. eauto. }
  unfold Int64.eq in Heq0. des_ifs. erewrite Int64.unsigned_zero in e.
  erewrite Int64.unsigned_repr in e; try lia.
  { unfold Int64.max_unsigned, Ptrofs.max_unsigned in *. erewrite <- Ptrofs.modulus_eq64; eauto. lia. }
Qed.

Lemma external_pc_fsim
    b ef m rs rs'
    (MCHAR: mem_char_all prog m)
    (SPC: rs PC = Vptr b Ptrofs.zero)
    (INT: Genv.find_funct_ptr ge b = Some (External ef))
    (RCEXT : rs_binded m rs rs'):
  Mem.to_ptr (rs' PC) m = Some (Vptr b Ptrofs.zero).
Proof.
  inv MCHAR. r in H0. exploit H0; eauto. i. des.
  dup RCEXT. specialize (RCEXT0 PC). rewrite SPC in RCEXT0. inv RCEXT0; ss.
  des_ifs_safe. exploit Mem.ptr2int_to_denormalize_max; eauto.
  { eapply Ptrofs.unsigned_range_2. }
  i. des. exploit Mem.denormalize_info; eauto. i. des.
  erewrite Int64.unsigned_repr.
  2:{ unfold Int64.max_unsigned, Ptrofs.max_unsigned in *. erewrite <- Ptrofs.modulus_eq64; eauto. lia. }
  des_ifs.
  unfold Int64.eq in Heq0. des_ifs. erewrite Int64.unsigned_zero in e.
  erewrite Int64.unsigned_repr in e; try lia.
  { unfold Int64.max_unsigned, Ptrofs.max_unsigned in *. erewrite <- Ptrofs.modulus_eq64; eauto. lia. }
Qed.

Lemma goto_label_fsim
    m1 m1' m2 rs1 rs2 b ofs f l i rs1'
    (CHAR: mem_char_all prog m2)
    (SPC: rs1 PC = Vptr b ofs)
    (INT: Genv.find_funct_ptr ge b = Some (Internal f))
    (FIND: find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i)
    (EXEC: goto_label f l rs1 m1 = Next rs1' m1')
    (MCEXT: concrete_extends m1 m2)
    (RCEXT: rs_binded m2 rs1 rs2):
  exists rs2' m2',
    Lowerbound.goto_label f l rs2 m2 = Next rs2' m2' /\ concrete_extends m1' m2' /\ rs_binded m2' rs1' rs2'.
Proof.
  exploit internal_pc_fsim; eauto. i. unfold goto_label in EXEC. des_ifs.
  unfold Lowerbound.goto_label. erewrite Heq, H. esplits; eauto. eapply set_bind; eauto. econs.
Qed.
  
Lemma exec_instr_fsim
    f i rs1 rs2 m1 m2 rs1' m1' b ofs
    (CHAR: mem_char_all prog m2)
    (SPC: rs1 PC = Vptr b ofs)
    (INT: Genv.find_funct_ptr ge b = Some (Internal f))
    (FIND: find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i)
    (EXEC: Asm.exec_instr ge f i rs1 m1 = Next rs1' m1')
    (MCEXT: concrete_extends m1 m2)
    (RCEXT: rs_binded m2 rs1 rs2):
  exists rs2' m2',
    Lowerbound.exec_instr ge f i rs2 m2 = Next rs2' m2'
  /\ concrete_extends m1' m2'
  /\ rs_binded m2' rs1' rs2'.
Proof.
  destruct i; ss; try by clarify;
    match goal with
    | H: exec_load _ _ _ _ _ _ = Next _ _ |- _ => (try by exploit exec_load_fsim; eauto)
    | H: exec_store _ _ _ _ _ _ _ = Next _ _ |- _ => (try by exploit exec_store_fsim; eauto)
    | _ => idtac
    end.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply zero_ext_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply sign_ext_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply zero_ext_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply sign_ext_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply longofintu_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply longofint_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply loword_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply singleoffloat_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply floatofsingle_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply intoffloat_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply floatofint_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply intofsingle_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply singleofint_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply longoffloat_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply floatoflong_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply longofsingle_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply singleoflong_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply addrmode32_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto.
    eapply addrmode64_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto.
    eapply set_bind; eauto. specialize (RCEXT rd). unfold Val.neg. des_ifs; inv RCEXT; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto.
    eapply set_bind; eauto. specialize (RCEXT rd). unfold Val.negl. des_ifs; inv RCEXT; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto.
    eapply set_bind; eauto. eapply add_bind; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto.
    eapply set_bind; eauto. eapply addl_bind; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto.
    eapply set_bind; eauto. eapply sub_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto.
    eapply set_bind; eauto. eapply subl_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto.
    eapply set_bind; eauto. eapply psub_join_asm_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto.
    eapply set_bind; eauto. eapply mul_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto.
    eapply set_bind; eauto. eapply mull_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto.
    eapply set_bind; eauto. eapply mul_bind; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto.
    eapply set_bind; eauto. eapply mull_bind; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto.
    eapply set_bind.
    + unfold Val.mulhs. dup RCEXT. specialize (RCEXT RAX). specialize (RCEXT0 r1).
      des_ifs; inv RCEXT; inv RCEXT0; try econs.
    + eapply set_bind; eauto. eapply mul_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto.
    eapply set_bind.
    + unfold Val.mullhs. dup RCEXT. specialize (RCEXT RAX). specialize (RCEXT0 r1).
      des_ifs; inv RCEXT; inv RCEXT0; try econs.
    + eapply set_bind; eauto. eapply mull_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. 
    eapply set_bind.
    + unfold Val.mullhs. dup RCEXT. specialize (RCEXT RAX). specialize (RCEXT0 r1).
      des_ifs; inv RCEXT; inv RCEXT0; try econs.
    + eapply set_bind; eauto. eapply mul_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto.
    eapply set_bind.
    + unfold Val.mullhs. dup RCEXT. specialize (RCEXT RAX). specialize (RCEXT0 r1).
      des_ifs; inv RCEXT; inv RCEXT0; try econs.
    + eapply set_bind; eauto. eapply mull_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    unfold Val.shr. specialize (RCEXT RAX). des_ifs; inv RCEXT; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    unfold Val.shrl. specialize (RCEXT RAX). des_ifs; inv RCEXT; try econs.
  - des_ifs_safe. dup RCEXT. dup RCEXT0. dup RCEXT1.
    specialize (RCEXT RDX). specialize (RCEXT0 RAX). specialize (RCEXT1 r1).
    rewrite Heq in RCEXT. rewrite Heq0 in RCEXT0. rewrite Heq1 in RCEXT1.
    inv RCEXT; inv RCEXT0; inv RCEXT1. erewrite Heq2.
    esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto; [econs|].
    eapply set_bind; eauto. econs.
  - des_ifs_safe. dup RCEXT. dup RCEXT0. dup RCEXT1.
    specialize (RCEXT RDX). specialize (RCEXT0 RAX). specialize (RCEXT1 r1).
    rewrite Heq in RCEXT. rewrite Heq0 in RCEXT0. rewrite Heq1 in RCEXT1.
    inv RCEXT; inv RCEXT0; inv RCEXT1. erewrite Heq2.
    esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto; [econs|].
    eapply set_bind; eauto. econs.
  - des_ifs_safe. dup RCEXT. dup RCEXT0. dup RCEXT1.
    specialize (RCEXT RDX). specialize (RCEXT0 RAX). specialize (RCEXT1 r1).
    rewrite Heq in RCEXT. rewrite Heq0 in RCEXT0. rewrite Heq1 in RCEXT1.
    inv RCEXT; inv RCEXT0; inv RCEXT1. erewrite Heq2.
    esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto; [econs|].
    eapply set_bind; eauto. econs.
  - des_ifs_safe. dup RCEXT. dup RCEXT0. dup RCEXT1.
    specialize (RCEXT RDX). specialize (RCEXT0 RAX). specialize (RCEXT1 r1).
    rewrite Heq in RCEXT. rewrite Heq0 in RCEXT0. rewrite Heq1 in RCEXT1.
    inv RCEXT; inv RCEXT0; inv RCEXT1. erewrite Heq2.
    esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto; [econs|].
    eapply set_bind; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    unfold Val.and. dup RCEXT. specialize (RCEXT rd). specialize (RCEXT0 r1).
    des_ifs; inv RCEXT; inv RCEXT0; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    unfold Val.andl. dup RCEXT. specialize (RCEXT rd). specialize (RCEXT0 r1).
    des_ifs; inv RCEXT; inv RCEXT0; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    unfold Val.and. specialize (RCEXT rd). des_ifs; inv RCEXT; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    unfold Val.andl. specialize (RCEXT rd). des_ifs; inv RCEXT; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    dup RCEXT. specialize (RCEXT rd). specialize (RCEXT0 r1). des_ifs; inv RCEXT; inv RCEXT0; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    dup RCEXT. specialize (RCEXT rd). specialize (RCEXT0 r1). des_ifs; inv RCEXT; inv RCEXT0; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    specialize (RCEXT rd). des_ifs; inv RCEXT; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    specialize (RCEXT rd). des_ifs; inv RCEXT; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    dup RCEXT. specialize (RCEXT rd). specialize (RCEXT0 r1). des_ifs; inv RCEXT; inv RCEXT0; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    dup RCEXT. specialize (RCEXT rd). specialize (RCEXT0 r1). des_ifs; inv RCEXT; inv RCEXT0; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    specialize (RCEXT rd). des_ifs; inv RCEXT; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    specialize (RCEXT rd). des_ifs; inv RCEXT; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    specialize (RCEXT rd). des_ifs; inv RCEXT; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    specialize (RCEXT rd). des_ifs; inv RCEXT; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    dup RCEXT. specialize (RCEXT rd). specialize (RCEXT0 RCX). des_ifs; inv RCEXT; inv RCEXT0; try econs.
    eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    dup RCEXT. specialize (RCEXT rd). specialize (RCEXT0 RCX). des_ifs; inv RCEXT; inv RCEXT0; try econs.
    eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    specialize (RCEXT rd). des_ifs; inv RCEXT; try econs. eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    specialize (RCEXT rd). des_ifs; inv RCEXT; try econs. eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    dup RCEXT. specialize (RCEXT rd). specialize (RCEXT0 RCX). des_ifs; inv RCEXT; inv RCEXT0; try econs.
    eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    dup RCEXT. specialize (RCEXT rd). specialize (RCEXT0 RCX). des_ifs; inv RCEXT; inv RCEXT0; try econs.
    eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    specialize (RCEXT rd). des_ifs; inv RCEXT; try econs. eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    specialize (RCEXT rd). des_ifs; inv RCEXT; try econs. eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    dup RCEXT. specialize (RCEXT rd). specialize (RCEXT0 RCX). des_ifs; inv RCEXT; inv RCEXT0; try econs.
    eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    dup RCEXT. specialize (RCEXT rd). specialize (RCEXT0 RCX). des_ifs; inv RCEXT; inv RCEXT0; try econs.
    eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    specialize (RCEXT rd). des_ifs; inv RCEXT; try econs. eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    specialize (RCEXT rd). des_ifs; inv RCEXT; try econs. eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    dup RCEXT. specialize (RCEXT rd). specialize (RCEXT0 r1).
    des_ifs; inv RCEXT; inv RCEXT0; try econs; try eapply  val_intptr_refl.
    + simpl. des_ifs.
    + ss. des_ifs; ss; econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    specialize (RCEXT rd). des_ifs; inv RCEXT; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto.
    specialize (RCEXT rd). des_ifs; inv RCEXT; try econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply compare_ints_binded; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply compare_longs_binded; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply compare_ints_binded; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply compare_longs_binded; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto.
    eapply compare_ints_binded; eauto; [|econs]. eapply and_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto.
    eapply compare_longs_binded; eauto; [|econs]. eapply andl_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto.
    eapply compare_ints_binded; eauto; [|econs]. eapply and_bind; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto.
    eapply compare_longs_binded; eauto; [|econs]. eapply andl_bind; eauto. econs.
  - destruct (eval_testcond c rs1) eqn:TEST1.
    2:{ inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. econs. }
    exploit eval_testcond_bind; eauto. i. rewrite H.
    inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. des_ifs; eauto.
  - destruct (eval_testcond c rs1) eqn:TEST1.
    2:{ inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. econs. }
    exploit eval_testcond_bind; eauto. i. rewrite H.
    inv EXEC. esplits; eauto. ss. eapply nextinstr_sim; eauto. eapply set_bind; eauto. eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. eapply addf_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. eapply subf_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. eapply mulf_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. eapply divf_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. eapply negf_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. eapply absf_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply compare_floats_binded; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto. econs.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. eapply addfs_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. eapply subfs_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. eapply mulfs_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. eapply divfs_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. eapply negfs_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply set_bind; eauto. eapply absfs_bind; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto. eapply compare_floats32_binded; eauto.
  - inv EXEC. esplits; eauto. eapply nextinstr_nf_sim; eauto. eapply set_bind; eauto. econs.
  - exploit goto_label_fsim; eauto.
  - inv EXEC. esplits; eauto. eapply set_bind; eauto. eapply val_intptr_refl.
  - inv EXEC. esplits; eauto. unfold to_ptr. des_ifs.
    2:{ eapply set_bind; eauto. econs. }
    eapply set_bind; eauto. specialize (RCEXT r). inv RCEXT; (try by (rewrite <- H0 in Heq; ss)); ss.
    + rewrite <- H0 in Heq. ss. des_ifs.
      { eapply Int64.same_if_eq in Heq1. subst. econs. }
      econs; eauto. ss. exploit Mem.denormalize_info; eauto. i. des.
      rewrite Ptrofs.unsigned_repr; [|lia]. unfold Mem.ptr2int.
      exploit extended_concrete; eauto. i. rewrite H1. subst. des_ifs.
      do 2 f_equal. eapply Int64.same_if_eq. unfold Int64.eq.
      des_ifs. exfalso. eapply n.
      repeat rewrite Int64.unsigned_repr_eq.
      replace (caddr + (Int64.unsigned i - caddr)) with (Int64.unsigned i) by lia.
      rewrite <- Int64.unsigned_repr_eq. rewrite Int64.repr_unsigned. eauto.
    + erewrite <- H0 in Heq. ss. clarify. econs.
    + des_ifs. erewrite <- H in Heq. ss. clarify. econs; eauto. ss. des_ifs.
  - destruct (eval_testcond c rs1) eqn:TST; clarify.
    exploit eval_testcond_bind; eauto. i. rewrite H. destruct b0; ss.
    + exploit goto_label_fsim; eauto.
    + inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto.
  - destruct (eval_testcond c1 rs1) eqn:TST1; clarify.
    exploit eval_testcond_bind; eauto. i. rewrite H.
    destruct b0; destruct (eval_testcond c2 rs1) eqn:TST2; clarify.
    + exploit eval_testcond_bind; eauto. i. rewrite H0.
      destruct b0; ss.
      * exploit goto_label_fsim; eauto.
      * inv EXEC. esplits; eauto. eapply nextinstr_sim; eauto.
    + exploit eval_testcond_bind; eauto. i. rewrite H0.
      esplits; eauto. eapply nextinstr_sim; eauto.
  - destruct (rs1 r) eqn:R; try by (ss; clarify).
    exploit RCEXT. instantiate (1:=r). i. rewrite R in H. inv H. des_ifs.
    exploit goto_label_fsim; try eapply EXEC; eauto. repeat (eapply set_bind; try by econs). eauto.
  - inv EXEC. esplits; eauto. eapply set_bind.
    { eapply val_intptr_refl. }
    eapply set_bind; eauto. eapply pc_add_one_bind; eauto.
  - inv EXEC. esplits; eauto. eapply set_bind.
    { specialize (RCEXT r). inv RCEXT; unfold to_ptr; ss; try by econs.
      des_ifs.
      { eapply Int64.same_if_eq in Heq1. subst. eapply val_intptr_refl. }
      2:{ econs. }
      econs; eauto. ss. exploit Mem.denormalize_info; eauto. i. des.
      unfold Mem.ptr2int. exploit extended_concrete; eauto. i. rewrite H1. des_ifs.
      do 2 f_equal. eapply Int64.same_if_eq. unfold Int64.eq.
      des_ifs. exfalso. eapply n.
      repeat rewrite Int64.unsigned_repr_eq. repeat rewrite Ptrofs.unsigned_repr_eq.
      rewrite Ptrofs.modulus_eq64; eauto. rewrite Zplus_mod_idemp_r.
      replace (caddr + (Int64.unsigned i - caddr)) with (Int64.unsigned i) by lia.
      rewrite <- Int64.unsigned_repr_eq. rewrite Int64.repr_unsigned. eauto. }
    eapply set_bind; eauto. eapply pc_add_one_bind; eauto.
  - inv EXEC. esplits; eauto. eapply set_bind; eauto.
  - inv EXEC. esplits; eauto. eapply set_bind; eauto.
    eapply pc_add_one_bind; eauto.
  - des_ifs_safe. exploit alloc_concrete_extends; eauto. i. des.
    rewrite Heq in FREE. clarify.
    exploit store_concrete_extends; try eapply Heq1; eauto.
    { eapply alloc_val_intptr; eauto. }
    i. des.
    exploit store_concrete_extends; try eapply Heq2; eauto.
    { instantiate (1:=rs2 RA). eapply store_val_intptr; eauto. eapply alloc_val_intptr; eauto. }
    i. des. erewrite STORE, STORE0. esplits; eauto.
    eapply nextinstr_sim; eauto. eapply set_bind.
    { econs. }
    eapply set_bind; eauto.
    { eapply store_val_intptr; eauto. eapply store_val_intptr; eauto. eapply alloc_val_intptr; eauto. }
    ii. eapply store_val_intptr; eauto. eapply store_val_intptr; eauto. eapply alloc_val_intptr; eauto.
  - des_ifs_safe.
    exploit loadv_concrete_extends; try eapply Heq; eauto.
    { rewrite <- Heq1. eapply pc_add_delta_bind; eauto. }
    i. des.
    exploit loadv_concrete_extends; try eapply Heq0; eauto.
    { rewrite <- Heq1. eapply pc_add_delta_bind; eauto. }
    i. des. erewrite H, H1. 
    assert (to_ptr (val_add_ptrofs (rs2 RSP) ofs_ra) m2 = Val.offset_ptr (Vptr b0 i) ofs_ra).
    { unfold to_ptr. ss. unfold Mem.loadv in Heq. simpl. ss.
      exploit Mem.load_valid_access; eauto. i. eapply Mem.valid_access_perm with (k:=Cur) in H3.
      exploit to_ptr_concrete_exnteds. eauto.
      2:{ eapply Mem.perm_implies; eauto. econs. }
      { specialize (RCEXT RSP). eapply pc_add_delta_bind with (delta:=ofs_ra). eapply RCEXT. }
      { rewrite Heq1. ss. }
      i. erewrite H4. ss. }
    erewrite H3. ss. exploit free_concrete_extends; eauto. i. des.
    erewrite FREE; eauto. esplits; eauto.
    eapply set_bind.
    { eapply pc_add_one_bind. eapply free_val_intptr; eauto. eapply set_bind; eauto.
      eapply set_bind; eauto. }
    eapply set_bind; eauto.
    { eapply free_val_intptr; eauto. }
    eapply set_bind; eauto.
    { eapply free_val_intptr; eauto. }
    ii. eapply free_val_intptr; eauto.
Qed.

Lemma memval_concrete_extends
    m m' mv1 mv2
    (CEXT: forall b addr, m.(Mem.mem_concrete) ! b = Some addr -> m'.(Mem.mem_concrete) ! b = Some addr)
    (MVL: memval_intptr m mv1 mv2):
  memval_intptr m' mv1 mv2.
Proof.
  inv MVL; ss; try by econs.
  - des_ifs_safe. unfold Mem.ptr2int in Heq0. des_ifs.
    exploit CEXT; eauto. i. econs; eauto; ss.
    { ss. unfold Mem.ptr2int. erewrite H0. des_ifs. }
    ss.
  - inv H; ss; try by eapply memval_intptr_refl.
    2:{ econs. econs. }
    des_ifs. unfold Mem.ptr2int in Heq. des_ifs. exploit CEXT; eauto. i.
    econs. econs; eauto. ss. unfold Mem.ptr2int. rewrite H. des_ifs.
Qed.

Lemma val_intptr_concrete_extends
    m m' v1 v2
    (CEXT: forall b addr, m.(Mem.mem_concrete) ! b = Some addr -> m'.(Mem.mem_concrete) ! b = Some addr)
    (BIND: val_intptr m v1 v2):
  val_intptr m' v1 v2.
Proof.
  inv BIND; ss; try by econs. econs; eauto. ss.
  unfold Mem.ptr2int in *. des_ifs_safe. exploit CEXT; eauto. i. erewrite H0; ss.
Qed.

Lemma rs_binded_concrete_extends
    m m' rs1 rs2
    (CEXT: forall b addr, m.(Mem.mem_concrete) ! b = Some addr -> m'.(Mem.mem_concrete) ! b = Some addr)
    (RCEXT: rs_binded m rs1 rs2):
  rs_binded m' rs1 rs2.
Proof.
  ii. eapply val_intptr_concrete_extends; eauto.
Qed.

Lemma val_intptr_trans
    m v1 v2 v3
    (BIND1: val_intptr m v1 v2)
    (BIND2: val_intptr m v2 v3):
  val_intptr m v1 v3.
Proof.
  inv BIND1; inv BIND2; ss; try by econs.
Qed.

Lemma memval_intptr_trans
    m mv1 mv2 mv3
    (MVB1: memval_intptr m mv1 mv2)
    (MVB2: memval_intptr m mv2 mv3):
  memval_intptr m mv1 mv3.
Proof.
  inv MVB1; inv MVB2; ss; try by econs.
  { econs; eauto. }
  { inv H; econs; eauto. }
  { econs. eapply val_intptr_trans; eauto. }
  inv H. econs.
Qed.

Lemma memval_intptr_lbd_memval_intptr
    m mv1 mv2
    (MVBL: memval_intptr_lbd m mv1 mv2):
  memval_intptr m mv1 mv2.
Proof.
  unfold memval_intptr_lbd in MVBL. des_ifs; eauto; try by econs.
  { des; eauto. }
  { eapply memval_intptr_refl. }
Qed.

Lemma block_concretize_simulation
    m1 m2 rs1 rs2 m2'
    (MCEXT : concrete_extends m1 m2)
    (RCEXT : rs_binded m2 rs1 rs2)
    (MCONC: memory_block_concretize m2 m2'):
  concrete_extends m1 m2' /\ rs_binded m2' rs1 rs2.
Proof.
  split.
  - inv MCEXT. inv MCONC. des. econs.
    + erewrite same_nextblock. eauto.
    + i. eapply extended_access in H4.
      unfold Mem.perm in H4. erewrite H0 in H4. eauto.
    + i. rewrite <- H. exploit extended_contents; eauto. i.
      eapply memval_concrete_extends; eauto.
    + i. exploit extended_concrete; eauto.
  - inv MCONC. des. eapply rs_binded_concrete_extends; eauto.
Qed.

Lemma memory_concretize_contents_simulation
    m1 m2 rs1 rs2 m2'
    (MCEXT : concrete_extends m1 m2)
    (RCEXT : rs_binded m2 rs1 rs2)
    (MCONC: memory_concretize_contents m2 m2'):
  concrete_extends m1 m2' /\ rs_binded m2' rs1 rs2.
Proof.
  inv MCONC. des. splits; cycle 1.
  { eapply rs_binded_concrete_extends; try eapply RCEXT. i.
    rewrite <- H1; eauto. }
  inv MCEXT. econs.
  - rewrite same_nextblock; eauto.
  - i. eapply extended_access in H3. unfold Mem.perm. rewrite <-H. eauto.
  - i. specialize (H2 b ofs). eapply extended_contents in H3.
    eapply same_concrete_memval_intptr in H3; eauto. des_safe.
    eapply memval_intptr_trans; eauto.
    eapply memval_intptr_lbd_memval_intptr; eauto.
  - i. rewrite <- H1. eauto.
Qed.

Lemma register_concretizer_simulation
    m rs1 rs2 rs2'
    (RCEXT : rs_binded m rs1 rs2)
    (RCONC: register_concretizer m rs2 rs2'):
  rs_binded m rs1 rs2'.
Proof.
  ii. specialize (RCEXT r). specialize (RCONC r). des_ifs; inv RCEXT; (try by econs);
    try (rewrite <- RCONC; econs; eauto).
  des. eauto.
Qed.

Lemma cstep_simulation
     S1 S2 S2'
    (MS: match_states S1 S2)
    (CSTEP: cstep S2 S2'):
  match_states S1 S2'.
Proof.
  inv CSTEP. inv MS.
  exploit block_concretize_simulation; eauto. i. des.
  exploit memory_concretize_contents_simulation; try eapply H; eauto. i. des.
  eapply register_concretizer_simulation in H2; eauto. econs; eauto.
Qed.

Definition ge_binded_state (ge: genv) (st: Lowerbound.state) (gm: positive -> option Z) : Prop :=
  ge_binded ge (Lowerbound.state_mem st) gm.

Lemma ge_binded_state_astep
    st st' tr gm
    (BIND: ge_binded_state ge st gm)
    (STEP: astep ge st tr st'):
  ge_binded_state ge st' gm.
Proof.
  unfold ge_binded_state in *. inv STEP; ss. 
  - destruct i; ss; try by clarify;
    match goal with
    | H: Lowerbound.exec_load _ _ _ _ _ _ = Next _ _ |- _ => (unfold Lowerbound.exec_load in *; des_ifs)
    | H: Lowerbound.exec_store _ _ _ _ _ _ _ = Next _ _ |- _ =>
        (unfold Lowerbound.exec_store, Mem.storev in *; des_ifs; eapply ge_binded_store; eauto; ss)
    | _ => idtac
    end; try by des_ifs.
    + unfold Lowerbound.goto_label in H2. des_ifs.
    + unfold Lowerbound.goto_label in H2. des_ifs.
    + unfold Lowerbound.goto_label in H2. des_ifs.
    + unfold Lowerbound.goto_label in H2. des_ifs.
    + des_ifs. eapply ge_binded_alloc in Heq; eauto.
      eapply ge_binded_store in Heq0; eauto. eapply ge_binded_store; eauto.
    + des_ifs. eapply ge_binded_free; eauto.
  - eapply ge_binded_external_call; eauto.
  - eapply ge_binded_external_call; eauto.
Qed.

Lemma ge_binded_block_concretize
    m m' gm
    (BIND: ge_binded ge m gm)
    (CONC : memory_block_concretize m m'):
  ge_binded ge m' gm.
Proof.
  unfold ge_binded in *. i. exploit BIND; eauto. i. des. esplits; eauto.
  inv CONC. des. rewrite H2 in *. eauto.
Qed.

Lemma ge_binded_state_cstep
    st st' gm
    (BIND: ge_binded_state ge st gm)
    (STEP: cstep st st'):
  ge_binded_state ge st' gm.
Proof.
  inv STEP. unfold ge_binded_state in *. ss.
  eapply ge_binded_block_concretize in CONC; eauto. inv CCONC. des.
  unfold ge_binded in CONC. ii. exploit CONC; eauto. i. des. esplits; eauto.
  rewrite <- H1; eauto.
Qed.

Lemma ge_binded_state_step
    st st' tr gm
    (BIND: ge_binded_state ge st gm)
    (STEP: Lowerbound.step ge st tr st'):
  ge_binded_state ge st' gm.
Proof.
  inv STEP.
  - eapply ge_binded_state_cstep; try eapply CSTEP. eapply ge_binded_state_astep; eauto.
  - eapply ge_binded_state_astep; eauto.
Qed.

Lemma eval_builtin_arg_bind
    m m' rs rs' arg varg
    (MCEXT: concrete_extends m m')
    (RCEXT: rs_binded m' rs rs')
    (SRC: Events.eval_builtin_arg ge rs (rs RSP) m arg varg):
  exists varg', eval_builtin_arg PregEq.t ge rs' (rs' RSP) m' arg varg' /\ val_intptr m' varg varg'.
Proof.
  move SRC before ICAP1. revert_until ICAP1. induction 1; i; ss.
  - esplits; eauto. econs.
  - esplits; eauto. econs. econs.
  - esplits; eauto. econs. econs.
  - esplits; eauto. econs. econs.
  - esplits; eauto. econs. econs.
  - exploit loadv_concrete_extends; try eapply H; eauto.
    { eapply pc_add_delta_bind. eauto. }
    i. des. esplits; eauto. econs; eauto.
  - esplits; eauto; try by econs. eapply pc_add_delta_bind. eauto.
  - exploit loadv_concrete_extends; try eapply H; eauto.
    { eapply val_intptr_refl. }
    i. des. esplits; eauto. econs; eauto.
  - esplits; eauto. econs. eapply val_intptr_refl.
  - exploit IHSRC1; eauto. i. des. exploit IHSRC2; eauto. i. des. esplits. econs; eauto.
    eapply longofwords_bind; eauto.
  - exploit IHSRC1; eauto. i. des. exploit IHSRC2; eauto. i. des. esplits. econs; eauto.
    destruct Archi.ptr64.
    + eapply addl_bind; eauto.
    + eapply add_bind; eauto.
Qed.

Lemma eval_builtin_arg_determ_lbd
    m rs arg varg1
    (ARG1: eval_builtin_arg PregEq.t ge rs (rs RSP) m arg varg1)
    varg2 (ARG2: eval_builtin_arg PregEq.t ge rs (rs RSP) m arg varg2):
  varg2 = varg1.
Proof.
  revert_until ICAP1. induction 1; i; try by (inv ARG2; eauto; Eq).
  - inv ARG2. eapply IHARG1_1 in H1. subst. eapply IHARG1_2 in H3. subst. eauto.
  - inv ARG2. eapply IHARG1_1 in H1. subst. eapply IHARG1_2 in H3. subst. eauto.
Qed.

Lemma eval_builtin_args_bind
    m m' rs rs' args vargs
    (MCEXT: concrete_extends m m')
    (RCEXT: rs_binded m' rs rs')
    (SRC: Events.eval_builtin_args ge rs (rs RSP) m args vargs):
  exists vargs', eval_builtin_args PregEq.t ge rs' (rs' RSP) m' args vargs' /\ val_intptrist m' vargs vargs'.
Proof.
  revert SRC. revert args vargs. induction 1; i.
  { esplits; eauto; econs. }
  des. exploit eval_builtin_arg_bind; eauto. i. des. esplits; eauto.
  { econs; eauto. }
  econs; eauto.
Qed.

Lemma eval_builtin_args_determ_lbd
    m rs arg varg1
    (ARG1: eval_builtin_args PregEq.t ge rs (rs RSP) m arg varg1)
    varg2 (ARG2: eval_builtin_args PregEq.t ge rs (rs RSP) m arg varg2):
  varg2 = varg1.
Proof.
  revert_until ICAP1. induction 1; i; try by (inv ARG2; eauto; Eq).
  inv ARG2. exploit eval_builtin_arg_determ_lbd. eapply H. eapply H2. i. subst.
  exploit IHARG1; eauto. i. subst. eauto.
Qed.

Lemma extcall_arg_bind
    m m' rs rs' l v1
    (MCEXT: concrete_extends m m')
    (RCEXT: rs_binded m' rs rs')
    (SRC: Asm.extcall_arg rs m l v1):
  exists v2, Lowerbound.extcall_arg rs' m' l v2 /\ val_intptr m' v1 v2.
Proof.
  inv SRC.
  - esplits. econs. eauto.
  - exploit loadv_concrete_extends; try eapply H0; eauto.
    { eapply pc_add_delta_bind. eauto. }
    i. des. esplits; eauto. econs; eauto.
Qed.

Lemma extcall_arg_pair_bind
    m m' rs rs' l v1
    (MCEXT: concrete_extends m m')
    (RCEXT: rs_binded m' rs rs')
    (SRC: Asm.extcall_arg_pair rs m l v1):
  exists v2, Lowerbound.extcall_arg_pair rs' m' l v2 /\ val_intptr m' v1 v2.
Proof.
  revert SRC. revert l v1. induction 1; i.
  - exploit extcall_arg_bind; eauto. i. des. esplits; eauto. econs. eauto.
  - eapply extcall_arg_bind in H; eauto. eapply extcall_arg_bind in H0; eauto. des.
    esplits. econs; eauto. eapply longofwords_bind; eauto.
Qed.

Lemma extcall_arg_pair_list_bind
    m m' rs rs' l v1
    (MCEXT: concrete_extends m m')
    (RCEXT: rs_binded m' rs rs')
    (SRC: list_forall2 (Asm.extcall_arg_pair rs m) l v1):
  exists v2, list_forall2 (Lowerbound.extcall_arg_pair rs' m') l v2 /\ val_intptrist m' v1 v2.
Proof.
  revert SRC. revert l v1. induction 1; i.
  { esplits; econs. }
  des. exploit extcall_arg_pair_bind; eauto. i. des. esplits; econs; eauto.
Qed.

Lemma extcall_arguments_bind
    m m' rs rs' ef args
    (MCEXT: concrete_extends m m')
    (RCEXT: rs_binded m' rs rs')
    (SRC: extcall_arguments rs m (ef_sig ef) args):
  exists args', Lowerbound.extcall_arguments rs' m' (ef_sig ef) args' /\ val_intptrist m' args args'.
Proof.
  exploit extcall_arg_pair_list_bind; eauto.
Qed.
  
Theorem astep_simulation:
  forall S1' t' S2', astep ge S1' t' S2' ->
  forall S1 (SAFE: safe sem S1) (IBIND: ge_binded_state ge S1' gmtgt) (TCHAR: state_char prog S1') (MS: match_states S1 S1'),
  (exists t S2, tr_rel (ev_rel gmtgt) t t' /\ Step sem S1 t S2 /\ match_states S2 S2')
\/ (exists t S2, (~ trace_intact t')
         /\ Star sem S1 t S2
         /\ exists tl, tr_rel (ev_rel gmtgt) t (trace_cut_pterm t' ** tl)).
Proof.
  induction 1; ss. i.
  - left. exists E0. inv MS.
    specialize (SAFE _ (star_refl _ _ _)). des.
    { inv SAFE. specialize (RCEXT PC). rewrite H5 in RCEXT. inv RCEXT. des_ifs.
      rewrite <- H6 in H. rewrite <- Heq in H. ss. }
    assert (rs0 PC = Vptr b ofs).
    { r in TCHAR. ss. inv SAFE.
      + exploit internal_pc_fsim; eauto. i. clarify.
      + exploit internal_pc_fsim; eauto. i. clarify.
      + exploit external_pc_fsim; eauto. i. clarify. }
    inv SAFE; Eq; ss; fold ge in H7; Eq; ss.
    fold ge in H11.
    exists (State rs'0 m'0). esplits; [econs| |].
    { econs; eauto. }
    { exploit exec_instr_fsim; eauto. i. des. ss. Eq.
      econs; eauto. }
  - i. inv MS.
    specialize (SAFE _ (star_refl _ _ _)). des.
    { inv SAFE. specialize (RCEXT PC). rewrite H6 in RCEXT. inv RCEXT. des_ifs.
      rewrite <- H7 in H. rewrite <- Heq in H. ss. }
    assert (rs0 PC = Vptr b ofs).
    { r in TCHAR. ss. inv SAFE.
      + exploit internal_pc_fsim; eauto. i. clarify.
      + exploit internal_pc_fsim; eauto. i. clarify.
      + exploit external_pc_fsim; eauto. i. clarify. }
    inv SAFE; Eq; ss; fold ge in H8; Eq; ss.
    assert (BINDARGS: val_intptrist m vargs0 vargs).
    { exploit eval_builtin_args_bind; eauto. i. des.
      exploit eval_builtin_args_determ_lbd. eapply H2. fold ge. eapply H5. i. subst. eauto. }
    (* MOVE THIS TO Events.v *)
    assert (BWD: extcall_properties_backward (external_call ef0) (ef_sig ef0)).
    { destruct (classic (is_external_ef ef0)).
      { eapply external_call_spec_backward. eauto. }
      eapply forwrard_axiom_implies_backward_axiom. eapply external_call_spec. eauto. }
    exploit ec_concrete_extends_backward; try eapply MCEXT; eauto.
    i. des.
    + left. esplits; eauto. econs 2; eauto.
      econs; eauto. eapply nextinstr_nf_sim. eapply set_res_bind; eauto. eapply undef_regs_binded; eauto.
      ii. eapply val_intptr_concrete_extends.
      { eapply ec_binds; eauto. eapply external_call_common_spec. }
      eauto.
    + eapply UBSRC in H11. contradiction.
    + right. esplits; eauto. eapply star_one. econs 2; eauto.
  - i. inv MS.
    specialize (SAFE _ (star_refl _ _ _)). des.
    { inv SAFE. specialize (RCEXT PC). rewrite H5 in RCEXT. inv RCEXT. des_ifs.
      rewrite <- H6 in H. rewrite <- Heq in H. ss. }
    assert (rs0 PC = Vptr b Ptrofs.zero).
    { r in TCHAR. ss. inv SAFE.
      + exploit internal_pc_fsim; eauto. i. clarify.
      + exploit internal_pc_fsim; eauto. i. clarify.
      + exploit external_pc_fsim; eauto. i. clarify. }
    inv SAFE; Eq; ss; fold ge in H7; Eq; ss.
    assert (BINDARGS: val_intptrist m args0 args).
    { exploit extcall_arguments_bind; eauto. i. des.
      exploit Lowerbound.extcall_arguments_determ. eapply H1. eapply H4. i. subst; eauto. }
    assert (BWD: extcall_properties_backward (external_call ef0) (ef_sig ef0)).
    { destruct (classic (is_external_ef ef0)).
      { eapply external_call_spec_backward. eauto. }
      eapply forwrard_axiom_implies_backward_axiom. eapply external_call_spec. eauto. }
    exploit ec_concrete_extends_backward; try eapply MCEXT; eauto.
    i. des.
    + left. esplits; eauto. econs 3; eauto.
      econs; eauto. eapply set_bind; eauto.
      { eapply val_intptr_concrete_extends. eapply ec_binds. eapply external_call_common_spec. eauto. eauto. }
      eapply set_pair_bind; eauto. unfold undef_caller_save_regs. ii. des_ifs; try by econs.
      { eapply val_intptr_concrete_extends. eapply ec_binds. eapply external_call_common_spec. eauto. eauto. }
    + eapply UBSRC in H9. contradiction.
    + right. esplits; eauto. eapply star_one. econs 3; eauto.
Qed.

Theorem step_simulation:
  forall S1' t' S2', Step tsem S1' t' S2' ->
  forall S1 (SAFE: safe sem S1) (IBIND: ge_binded_state ge S1' gmtgt) (TCHAR: state_char prog S1') (MS: match_states S1 S1'),
    (exists t S2, tr_rel (ev_rel gmtgt) t t' /\ Step sem S1 t S2 /\ match_states S2 S2')
  \/ (exists t S2, (~ trace_intact t')
           /\ Star sem S1 t S2
           /\ exists tl, tr_rel (ev_rel gmtgt) t (trace_cut_pterm t' ** tl)).
Proof.
  induction 1; ss; i.
  - exploit astep_simulation; eauto. i. des.
    + left. exploit cstep_simulation; try eapply CSTEP; eauto.
    + right. esplits; eauto.
  - exploit astep_simulation; eauto. i. des.
    + right.
      exploit tr_rel_cut_pterm; eauto.
      { i. destruct ev1, ev2; ss. }
      intros.
      do 2 eexists. splits.
      { subst. ii. eapply trace_intact_app_rev in H3. des.
        eapply INTACT1; ss. eauto. }
      { eapply star_one; eauto. }
      { specialize (trace_cut_pterm_split t). i. des.
        erewrite H3. erewrite OOMTR.
        replace (trace_cut_pterm (tr ++ [Event_pterm])) with (trace_cut_pterm tr).
        2:{ clear. ginduction tr; ss. rewrite <- IHtr. eauto. }
        exists t1. eapply tr_rel_app; eauto. eapply tr_rel_refl. eapply ev_rel_refl. }
    + right.
      eexists. eexists. splits.
      { subst. ii. eapply trace_intact_app_rev in H2. des; eauto. }
      { eauto. }
      { subst. 
        replace (trace_cut_pterm (tr ++ [Event_pterm])) with (trace_cut_pterm tr).
        2:{ clear. ginduction tr; ss. rewrite <- IHtr. eauto. }
        eauto. }
Qed.

Lemma lowerbound_progress
    S1 S2 tr S1'
    (GEBIND: ge_binded_state (Genv.globalenv prog) S2 gmtgt)
    (TCHAR: state_char prog S2)
    (MATCH: match_states S1 S2)
    (SAFESRC: Step (Asm.semantics prog) S1 tr S1'):
  exists tr' S2', Step (Lowerbound.semantics prog) S2 tr' S2'.
Proof.
  inv MATCH. inv SAFESRC; ss.
  - exploit internal_pc_fsim; eauto; i; ss.
    exploit exec_instr_fsim; eauto. i. des.
    assert (exists tr' S2', astep ge (Lowerbound.State rs' m') tr' S2').
    { esplits. econs; eauto. }
    des.
    destruct (classic (exists S2'', cstep S2' S2'')).
    { des. esplits. econs; eauto. }
    esplits. econs 2; eauto.
  - exploit internal_pc_fsim; eauto; i; ss.
    assert (BWD: extcall_properties_backward (external_call ef) (ef_sig ef)).
    { destruct (classic (is_external_ef ef)).
      - eapply external_call_spec_backward; eauto.
      - eapply forwrard_axiom_implies_backward_axiom. eapply external_call_spec. eauto. }
    exploit eval_builtin_args_bind; eauto. i. des.
    exploit ec_concrete_extends_backward_progress; eauto. i. des.
    assert (exists tr' S2', astep ge (Lowerbound.State rs' m') tr' S2').
    { esplits. econs 2; eauto. }
    des.
    destruct (classic (exists S2'', cstep S2' S2'')).
    { des. esplits. econs; eauto. }
    esplits. econs 2; eauto.
  - exploit external_pc_fsim; eauto; i; ss.
    assert (BWD: extcall_properties_backward (external_call ef) (ef_sig ef)).
    { destruct (classic (is_external_ef ef)).
      - eapply external_call_spec_backward; eauto.
      - eapply forwrard_axiom_implies_backward_axiom. eapply external_call_spec. eauto. }
    exploit extcall_arguments_bind; eauto. i. des.
    exploit ec_concrete_extends_backward_progress; eauto. i. des.
    assert (exists tr' S2', astep ge (Lowerbound.State rs' m') tr' S2').
    { esplits. econs 3; eauto. }
    des.
    destruct (classic (exists S2'', cstep S2' S2'')).
    { des. esplits. econs; eauto. }
    esplits. econs 2; eauto.
Qed.

Lemma final_state_determ: forall p st0 retv,
    Lowerbound.final_state st0 retv ->
    Dfinal_state (Lowerbound.semantics p) st0 retv.
Proof.
  econstructor; eauto.
  - intros. inv FINAL0; inv FINAL1; Eq; auto.
  - red. unfold not. intros.
    assert (NOSTEP: forall t st', ~ astep (Genv.globalenv p) st0 t st').
    { ii. inv FINAL. inv H1; try rewrite H2 in *; ss. }     
    inv FINAL; inv H0; simpl in *; Eq.
    + eapply NOSTEP; eauto.
    + eapply NOSTEP; eauto.
Qed.

Lemma final_state_fsim
    st_src0 st_tgt0 r
    (FINAL: Asm.final_state st_src0 r)
    (MS: match_states st_src0 st_tgt0):
  Lowerbound.final_state st_tgt0 r.
Proof.
  inv FINAL. inv MS. econs.
  { specialize (RCEXT PC). erewrite H in RCEXT. inv RCEXT; ss. }
  { specialize (RCEXT RAX). erewrite H0 in RCEXT. inv RCEXT; ss. }
Qed.

Lemma final_state_bsim
    st_src0 st_tgt0 r
    (SAFE: safe sem st_src0)
    (FINAL: Lowerbound.final_state st_tgt0 r)
    (TCHAR: state_char prog st_tgt0)
    (MS: match_states st_src0 st_tgt0):
  Asm.final_state st_src0 r.
Proof.
  specialize (SAFE _ (star_refl _ _ _)). des.
  2:{ unfold state_char in TCHAR. inv SAFE; inv MS; inv FINAL.
      - exploit internal_pc_fsim; eauto. i. ss. rewrite H5 in H3; ss.
      - exploit internal_pc_fsim; eauto. i. ss. rewrite H6 in H4; ss.
      - exploit external_pc_fsim; eauto. i. ss. rewrite H5 in H3; ss. }
  exploit final_state_fsim; eauto. i. exploit final_state_determ. eauto.
  instantiate (1:=prog). i. inv H0. exploit DTM; ss. eapply FINAL. eapply H. i. subst; eauto.
Qed.

Lemma initial_state_determ: forall st0 st1,
    initial_state_r prog st0 ->
    initial_state_r prog st1 -> st0 = st1.
Proof.
  intros. inv H; inv H0. inv INIT; inv INIT0; clarify.
  exploit realloc_globals_determ. eapply REA. eapply REA0. i. subst.
  subst ge ge0. subst rs2 rs0. eauto.
Qed.

Lemma match_states_xsim
    st_src0 st_tgt0
    (IBIND: ge_binded_state ge st_tgt0 gmtgt) (TCHAR: state_char prog st_tgt0)
    (MATCH: match_states st_src0 st_tgt0) :
  bsim sem tsem gmtgt lt 0%nat st_src0 st_tgt0.
Proof.
  generalize dependent st_src0. generalize dependent st_tgt0.
  pcofix CIH. i. pfold.
  econs. i. econs.
  - i. exploit step_simulation; eauto. i. destruct H; des_safe.
    { left. esplits; eauto. left. eapply plus_one; eauto.
      right. eapply CIH; eauto.
      - eapply ge_binded_state_step; eauto.
      - eapply state_char_preservation; eauto. }
    { right. esplits; eauto. }
  - ii. esplits; eauto.
    { eapply star_refl. }
    eapply final_state_bsim; eauto.
  - specialize (SAFESRC _ (star_refl _ _ _)). des.
    { exploit final_state_fsim; eauto. }
    right. eapply lowerbound_progress; eauto.
Qed.


End PRESERVATION.

Lemma transf_initial_states1
    prog st1 (INIT: Asm.initial_state prog st1):
  exists st2, Lowerbound.initial_state prog st2 /\ match_states st1 st2.
Proof.
  inv INIT. unfold ge in *. esplits.
  { econs. eauto. }
  subst rs0. econs.
  { eapply concrete_ext_refl. }
  eapply rs_binded_refl.
Qed.


(* move to Memory.v *)
Lemma nonempty_alloc_contents
  b lo hi m m'
  (NA: Mem.nonempty_alloc m b lo hi = Some m'):
  Mem.mem_contents m = Mem.mem_contents m'.
Proof. unfold Mem.nonempty_alloc in NA. des_ifs. Qed.

Lemma nonempty_alloc_access_neq
  b b' lo hi m m'
  (NEQ: b <> b')
  (NA: Mem.nonempty_alloc m b lo hi = Some m'):
  ((Mem.mem_access m) !! b') = ((Mem.mem_access m') !! b').
Proof. unfold Mem.nonempty_alloc in NA. des_ifs. ss. des_ifs. rewrite PMap.gso; eauto. Qed.

(* Lemma init_mem *)

Definition mem_char_init (prog: program) (m: mem) : Prop :=
  (forall b f, Genv.find_funct_ptr (Genv.globalenv prog) b = Some f -> Mem.perm m b 0 Cur Nonempty)
/\ (forall b, m.(Mem.mem_concrete) ! b = None).

Lemma init_mem_mem_char_init prog m
    (INIT: Genv.init_mem prog = Some m):
  mem_char_init prog m.
Proof.
  split; ii.
  - eapply Genv.init_mem_characterization_2 in H; eauto. des; eauto.
  - eapply Genv.init_mem_logical. eauto.
Qed.

Lemma init_mem_char_realloc_glob prog m b
    (INIT: mem_char_init prog m):
  exists m', realloc_global prog m b = Some m' /\ mem_char_init prog m'.
Proof.
  unfold realloc_global.
  destruct (Genv.find_funct_ptr (Genv.globalenv prog) b) eqn:FUNC.
  2:{ esplits; eauto. }
  des_ifs.
  2:{ esplits; eauto. }
  assert (exists m', Mem.nonempty_alloc m b 0 (function_length f0) = Some m').
  { r in INIT. inv INIT. exploit H; eauto. i. eapply Mem.perm_max in H1. unfold Mem.nonempty_alloc. des_ifs.
    specialize (H0 b). unfold Mem.is_concrete. esplits; eauto. }
  des. esplits; eauto. split; i.
  - destruct (peq b b0); cycle 1.
    + unfold Mem.perm in *. erewrite <- nonempty_alloc_access_neq; eauto.
      r in INIT. des. eapply INIT. eauto.
    + subst. specialize (function_length_pos f0). intros POS.
      exploit nonempty_nonempty_alloc; eauto.
      { lia. }
      { inv INIT. specialize (H2 b0). unfold Mem.is_concrete. rewrite H2. eauto. }
      instantiate (1:= Cur). i. des. exploit H1; eauto. lia.
  - inv INIT. erewrite <-Mem.nonempty_alloc_concrete; eauto.
Qed.

Lemma init_mem_char_realloc_glob_aux prog m bdd
    (INIT: mem_char_init prog m):
  exists m', _realloc_globals prog m bdd m' /\ mem_char_init prog m'.
Proof.
  revert INIT. revert m. induction bdd using positive_Peano_ind; i.
  { exploit init_mem_char_realloc_glob; eauto. instantiate (1:=1%positive). i. des.
    exists m'. esplits; eauto. econs; eauto. }
  exploit init_mem_char_realloc_glob; eauto. instantiate (1:= Pos.succ bdd). i. des.
  exploit IHbdd; eauto. i. des. exists m'0. esplits; eauto. econs 2; eauto.
  { eapply Pos.succ_not_1. }
  replace (Pos.succ bdd - 1)%positive with bdd by lia. eauto.
Qed.

Lemma init_mem_char_realloc_globals prog m
    (INIT: mem_char_init prog m):
  exists m', realloc_globals prog m m' /\ mem_char_init prog m'.
Proof.
  unfold realloc_globals. eapply init_mem_char_realloc_glob_aux; eauto.
Qed.

Lemma realloc_global_same_nextblock
    prog m m'
    (RA: realloc_globals prog m m'):
  Mem.nextblock m = Mem.nextblock m'.
Proof.
  r in RA. induction RA.
  - unfold realloc_global in RA. des_ifs. eapply Mem.nonempty_alloc_nextblock; eauto.
  - unfold realloc_global in RA. des_ifs. eapply Mem.nonempty_alloc_nextblock in RA; eauto.
    rewrite RA. eauto.
Qed.

Lemma realloc_global_same_concrete
    prog m m'
    (RA: realloc_globals prog m m'):
  Mem.mem_concrete m = Mem.mem_concrete m'.
Proof.
  r in RA. induction RA.
  - unfold realloc_global in RA. des_ifs. eapply Mem.nonempty_alloc_concrete; eauto.
  - unfold realloc_global in RA. des_ifs. eapply Mem.nonempty_alloc_concrete in RA; eauto.
    rewrite RA. eauto.
Qed.

Lemma realloc_global_same_contents
    prog m m'
    (RA: realloc_globals prog m m'):
  Mem.mem_contents m = Mem.mem_contents m'.
Proof.
  r in RA. induction RA.
  - unfold realloc_global in RA. des_ifs. eapply nonempty_alloc_contents; eauto.
  - unfold realloc_global in RA. des_ifs. eapply nonempty_alloc_contents in RA; eauto.
    rewrite RA. eauto.
Qed.


Lemma init_mem_realloc_glob prog m
  (INIT: Genv.init_mem prog = Some m):
  exists m', realloc_globals prog m m' /\ concrete_extends m m'.
Proof.
  exploit init_mem_mem_char_init; eauto. intros INITCHAR.
  exploit init_mem_char_realloc_globals; eauto. i. des. esplits; eauto.
  econs.
  - eapply realloc_global_same_nextblock; eauto.
  - i.
    destruct (classic (b <= Mem.nextblock m - 1)%positive).
    2:{ unfold realloc_globals in H.
        exploit nonempty_realloc_globals_not_range; try eapply H.
        { instantiate (1:=b). remember (Mem.nextblock m). lia. }
        i. unfold Mem.perm. rewrite <- H3. eauto. }
    destruct (Genv.find_funct_ptr (Genv.globalenv prog) b) eqn:FUNC.
    2:{ exploit nonempty_realloc_globals_not_func; eauto. i. 
        unfold Mem.perm. rewrite <- H3. eauto. }
    destruct f.
    { exploit nonempty_realloc_globals; try eapply H.
      { inv INITCHAR. eauto. }
      { eauto. }
      { eapply Genv.find_funct_ptr_not_fresh; eauto. }
      instantiate (1:= k). i. des.
      exploit Genv.init_mem_characterization_2; eauto. i. des.
      exploit H6; try eapply H1; eauto. i. des; subst.
      exploit H3; eauto.
      specialize (function_length_pos f). i. lia. }
    exploit nonempty_realloc_globals_external; eauto. i.
    unfold Mem.perm. rewrite <- H3. eauto.
  - i. eapply realloc_global_same_contents in H. rewrite H. eapply memval_intptr_refl.
  - i. eapply realloc_global_same_concrete in H. rewrite <- H. eauto.
Qed.
  
Lemma transf_initial_states2
    prog st1 (INIT: Asm.initial_state prog st1):
  exists st2, Lowerbound.initial_state_r prog st2 /\ match_states st1 st2.
Proof.
  exploit transf_initial_states1; eauto. i. des.
  inv INIT; inv H. Eq.
  assert (exists m', realloc_globals prog m1 m' /\ concrete_extends m1 m').
  { eapply init_mem_realloc_glob; eauto. }
  des. exists (Lowerbound.State rs1 m'). esplits.
  { econs; eauto. econs; eauto. }
  econs; eauto. subst rs0 rs1. eapply rs_binded_refl.
Qed.

Lemma transf_initial_capture1
  prog S1 S2 S2'
  (INITSRC: Asm.initial_state prog S1)
  (INITTGT: Lowerbound.initial_state_r prog S2)
  (MATCH: match_states S1 S2)
  (CAPTGT: Lowerbound.glob_capture prog S2 S2'):
  exists S1',
    Asm.glob_capture prog S1 S1'
    /\ match_states S1' S2'
    /\ gm_improves (Asm.concrete_snapshot (Genv.globalenv prog) S1') (Lowerbound.concrete_snapshot (Genv.globalenv prog) S2').
Proof.
  inv CAPTGT. inv MATCH.
  rewrite Genv.globalenv_public in CAPTURE.
  assert (exists m0', Genv.capture_init_mem m0 (Genv.non_static_glob (Genv.globalenv prog) (prog_public prog)) m0'
                 /\ concrete_extends m0' m').
  { inv CAPTURE. remember (prog_public prog) as lst. clear Heqlst. clear - MCEXT CAP.
    ginduction lst; ss; i.
    - inv CAP. esplits; eauto. econs; eauto. econs; eauto.
    - destruct (Genv.public_symbol (Genv.globalenv prog) a) eqn:PSYMB.
      2:{ exploit IHlst; eauto. }
      destruct (Genv.find_symbol (Genv.globalenv prog) a) eqn:PFIND.
      2:{ exploit IHlst; eauto. }
      i. inv CAP.
      exploit capture_concrete_extends; eauto. i. des. exploit IHlst; eauto. i. des.
      inv H. esplits; eauto. econs; eauto. econs; eauto. }
  des. esplits.
  - econs; eauto. rewrite Genv.globalenv_public. eauto.
  - econs; eauto. inv CAPTURE.
    ii. specialize (RCEXT r). eapply val_intptr_concrete_extends; try eapply RCEXT.
    i. eapply Mem.capture_list_prevaddr; eauto.
  - unfold concrete_snapshot, Lowerbound.concrete_snapshot. ii. des_ifs. ss.
    eapply extended_concrete; eauto.
Qed.

Lemma capture_mem_char_all
    prog m b addr m'
    (CHAR: mem_char_all prog m)
    (CAP: Mem.capture m b addr m'):
  mem_char_all prog m'.
Proof.
  inv CHAR. split; ii.
  - inv CAP. unfold Mem.perm. rewrite <- ACCESS. eauto.
  - inv CAP. unfold Mem.perm. rewrite <- ACCESS. eauto.
Qed.

Lemma capture_list_mem_char_all
    prog m bs addrs m'
    (CHAR: mem_char_all prog m)
    (CAP: Mem.capture_list m bs addrs m'):
  mem_char_all prog m'.
Proof.
  ginduction bs; i.
  { inv CAP. eauto. }
  inv CAP. exploit capture_mem_char_all; eauto.
Qed.

Lemma glob_capture_char
    p s s'
    (CHAR: state_char p s)
    (GCAP: Lowerbound.glob_capture p s s'):
  state_char p s'.
Proof.
  inv GCAP. inv CAPTURE. unfold state_char in *. ss.
  eapply capture_list_mem_char_all; eauto.
Qed.

Lemma glob_capture_c_char
    p s s'
    (CHAR: state_char p s)
    (GCAP: Lowerbound.glob_capture_c p s s'):
  state_char p s'.
Proof.
  inv GCAP. eapply state_char_preservation_cstep; try eapply CS.
  eapply glob_capture_char; eauto.
Qed.

Theorem lowerbound_correct prog:
  Simulation.backward_simulation (Asm.semantics prog) (Lowerbound.semantics prog).
Proof.
  econs. econs.
  - apply lt_wf.
  - i. ss. exploit transf_initial_states2; eauto.
    i. des. esplits; eauto.
  - ii. ss. exploit transf_initial_states2; eauto.
    i. des. exploit initial_state_determ. eapply INITTGT. eapply H. i. subst.
    inv TGTCAP.
    exploit transf_initial_capture1.
    { eapply INITSRC. }
    { eapply INITTGT. }
    { eauto. }
    { eauto. }
    i. des.
    exploit cstep_simulation.
    { eapply H2. }
    { eapply CS. }
    i.
    exists 0%nat. exists st_init_src_. exists S1'. exists (concrete_snapshot (Genv.globalenv prog) S1').
    esplits; eauto.
    { ii. eapply H3 in H5. unfold Lowerbound.concrete_snapshot in *. des_ifs.
      inv CS. inv CONC; inv CCONC. des; ss. rewrite <- H10. eauto. }
    eapply match_states_xsim; eauto.
    { ii. unfold gmtgt. ss. unfold Lowerbound.concrete_snapshot.
      unfold Senv.public_symbol, Senv.find_symbol. ss.
      rewrite H5, H6. split; eauto.
      inv GC.
      assert (In b (Genv.non_static_glob (Genv.globalenv prog) (Genv.genv_public (Genv.globalenv prog)))).
      { assert (In id (Genv.genv_public (Genv.globalenv prog))).
        { unfold Genv.public_symbol in H5. rewrite H6 in H5.
          destruct in_dec in H5; ss. }
        remember (Genv.genv_public (Genv.globalenv prog)) as l.
        clear - H7 H6 H5. ginduction l; ss; i; des; subst; eauto.
        - rewrite H6, H5. ss. eauto.
        - exploit IHl; eauto. i. des_ifs. ss. right. eapply H. }
      inv CAPTURE.
      exploit Mem.capture_list_concrete; eauto. i. des. exists addr. inv CS.
      inv CONC; inv CCONC. des. ss. rewrite <- H14; eauto. }
    exploit initial_state_char; eauto. i. exploit glob_capture_char; eauto. i.
    eapply state_char_preservation_cstep in CS; eauto.
Qed.

Theorem cstep_sanity_check
    s
    (CFAIL: forall s', ~ cstep s s'):
  forall m', ~ memory_block_concretize (Lowerbound.state_mem s) m'.
Proof.
  ii. destruct s; ss.
  assert (MCC: exists m'', memory_concretize_contents m' m'').
  { eapply memory_concretize_contents_exists_aux; eauto.
    inv H. des. i. eapply H4. unfold Mem.valid_block in *. rewrite H2. eauto. }
  des.
  assert (RCC: exists r', register_concretizer m'' r r').
  { eapply register_concretizer_exists. i.
    inv MCC. des. rewrite <- H2. inv H. des. eapply H8.
    unfold Mem.valid_block in *. rewrite H6, H1. eauto. }
  des.
  eapply CFAIL. econs; eauto.
Qed.

