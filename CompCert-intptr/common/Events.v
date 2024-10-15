(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Observable events, execution traces, and semantics of external calls. *)

Require Import String.
Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Builtins.
Require Import IntPtrRel.
Require Import sflib.
Require Import Classical.

(** * Events and traces *)

(** The observable behaviour of programs is stated in terms of
  input/output events, which represent the actions of the program
  that the external world can observe.  CompCert leaves much flexibility as to
  the exact content of events: the only requirement is that they
  do not expose memory states nor pointer values
  (other than pointers to global variables), because these
  are not preserved literally during compilation.  For concreteness,
  we use the following type for events.  Each event represents either:

- A system call (e.g. an input/output operation), recording the
  name of the system call, its parameters, and its result.

- A volatile load from a global memory location, recording the chunk
  and address being read and the value just read.

- A volatile store to a global memory location, recording the chunk
  and address being written and the value stored there.

- An annotation, recording the text of the annotation and the values
  of the arguments.

  The values attached to these events are of the following form.
  As mentioned above, we do not expose pointer values directly.
  Pointers relative to a global variable are shown with the name
  of the variable instead of the block identifier.
*)

Inductive eventval: Type :=
  | EVint: int -> eventval
  | EVlong: int64 -> eventval
  | EVfloat: float -> eventval
  | EVsingle: float32 -> eventval
  | EVptr_global: ident -> ptrofs -> eventval.

Inductive event: Type :=
  | Event_pterm: event
  | Event_syscall: string -> list eventval -> eventval -> event
  | Event_vload: memory_chunk -> ident -> ptrofs -> eventval -> event
  | Event_vstore: memory_chunk -> ident -> ptrofs -> eventval -> event
  | Event_annot: string -> list eventval -> event.

(** The dynamic semantics for programs collect traces of events.
  Traces are of two kinds: finite (type [trace]) or infinite (type [traceinf]). *)

Definition trace := list event.

Definition E0 : trace := nil.

Definition Eapp (t1 t2: trace) : trace := t1 ++ t2.

CoInductive traceinf : Type :=
  | Econsinf: event -> traceinf -> traceinf.

Fixpoint Eappinf (t: trace) (T: traceinf) {struct t} : traceinf :=
  match t with
  | nil => T
  | ev :: t' => Econsinf ev (Eappinf t' T)
  end.

(** Concatenation of traces is written [**] in the finite case
  or [***] in the infinite case. *)

Infix "**" := Eapp (at level 60, right associativity).
Infix "***" := Eappinf (at level 60, right associativity).

Lemma E0_left: forall t, E0 ** t = t.
Proof. auto. Qed.

Lemma E0_right: forall t, t ** E0 = t.
Proof. intros. unfold E0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma Eapp_assoc: forall t1 t2 t3, (t1 ** t2) ** t3 = t1 ** (t2 ** t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma Eapp_E0_inv: forall t1 t2, t1 ** t2 = E0 -> t1 = E0 /\ t2 = E0.
Proof (@app_eq_nil event).

Lemma E0_left_inf: forall T, E0 *** T = T.
Proof. auto. Qed.

Lemma Eappinf_assoc: forall t1 t2 T, (t1 ** t2) *** T = t1 *** (t2 *** T).
Proof.
  induction t1; intros; simpl. auto. decEq; auto.
Qed.

Hint Rewrite E0_left E0_right Eapp_assoc
             E0_left_inf Eappinf_assoc: trace_rewrite.

Opaque trace E0 Eapp Eappinf.

(** The following [traceEq] tactic proves equalities between traces
  or infinite traces. *)

Ltac substTraceHyp :=
  match goal with
  | [ H: (@eq trace ?x ?y) |- _ ] =>
       subst x || clear H
  end.

Ltac decomposeTraceEq :=
  match goal with
  | [ |- (_ ** _) = (_ ** _) ] =>
      apply (f_equal2 Eapp); auto; decomposeTraceEq
  | _ =>
      auto
  end.

Ltac traceEq :=
  repeat substTraceHyp; autorewrite with trace_rewrite; decomposeTraceEq.

(** Bisimilarity between infinite traces. *)

CoInductive traceinf_sim: traceinf -> traceinf -> Prop :=
  | traceinf_sim_cons: forall e T1 T2,
      traceinf_sim T1 T2 ->
      traceinf_sim (Econsinf e T1) (Econsinf e T2).

Lemma traceinf_sim_refl:
  forall T, traceinf_sim T T.
Proof.
  cofix COINDHYP; intros.
  destruct T. constructor. apply COINDHYP.
Qed.

Lemma traceinf_sim_sym:
  forall T1 T2, traceinf_sim T1 T2 -> traceinf_sim T2 T1.
Proof.
  cofix COINDHYP; intros. inv H; constructor; auto.
Qed.

Lemma traceinf_sim_trans:
  forall T1 T2 T3,
  traceinf_sim T1 T2 -> traceinf_sim T2 T3 -> traceinf_sim T1 T3.
Proof.
  cofix COINDHYP;intros. inv H; inv H0; constructor; eauto.
Qed.

CoInductive traceinf_sim': traceinf -> traceinf -> Prop :=
  | traceinf_sim'_cons: forall t T1 T2,
      t <> E0 -> traceinf_sim' T1 T2 -> traceinf_sim' (t *** T1) (t *** T2).

Lemma traceinf_sim'_sim:
  forall T1 T2, traceinf_sim' T1 T2 -> traceinf_sim T1 T2.
Proof.
  cofix COINDHYP; intros. inv H.
  destruct t. elim H0; auto.
Transparent Eappinf.
Transparent E0.
  simpl.
  destruct t. simpl. constructor. apply COINDHYP; auto.
  constructor. apply COINDHYP.
  constructor. unfold E0; congruence. auto.
Qed.

(** An alternate presentation of infinite traces as
  infinite concatenations of nonempty finite traces. *)

CoInductive traceinf': Type :=
  | Econsinf': forall (t: trace) (T: traceinf'), t <> E0 -> traceinf'.

Program Definition split_traceinf' (t: trace) (T: traceinf') (NE: t <> E0): event * traceinf' :=
  match t with
  | nil => _
  | e :: nil => (e, T)
  | e :: t' => (e, Econsinf' t' T _)
  end.
Next Obligation.
  elimtype False. elim NE. auto.
Qed.
Next Obligation.
  red; intro. elim (H e). rewrite H0. auto.
Qed.

CoFixpoint traceinf_of_traceinf' (T': traceinf') : traceinf :=
  match T' with
  | Econsinf' t T'' NOTEMPTY =>
      let (e, tl) := split_traceinf' t T'' NOTEMPTY in
      Econsinf e (traceinf_of_traceinf' tl)
  end.

Remark unroll_traceinf':
  forall T, T = match T with Econsinf' t T' NE => Econsinf' t T' NE end.
Proof.
  intros. destruct T; auto.
Qed.

Remark unroll_traceinf:
  forall T, T = match T with Econsinf t T' => Econsinf t T' end.
Proof.
  intros. destruct T; auto.
Qed.

Lemma traceinf_traceinf'_app:
  forall t T NE,
  traceinf_of_traceinf' (Econsinf' t T NE) = t *** traceinf_of_traceinf' T.
Proof.
  induction t.
  intros. elim NE. auto.
  intros. simpl.
  rewrite (unroll_traceinf (traceinf_of_traceinf' (Econsinf' (a :: t) T NE))).
  simpl. destruct t. auto.
Transparent Eappinf.
  simpl. f_equal. apply IHt.
Qed.

(** Prefixes of traces. *)

Definition trace_prefix (t1 t2: trace) :=
  exists t3, t2 = t1 ** t3.

Definition traceinf_prefix (t1: trace) (T2: traceinf) :=
  exists T3, T2 = t1 *** T3.

Lemma trace_prefix_app:
  forall t1 t2 t,
  trace_prefix t1 t2 ->
  trace_prefix (t ** t1) (t ** t2).
Proof.
  intros. destruct H as [t3 EQ]. exists t3. traceEq.
Qed.

Lemma traceinf_prefix_app:
  forall t1 T2 t,
  traceinf_prefix t1 T2 ->
  traceinf_prefix (t ** t1) (t *** T2).
Proof.
  intros. destruct H as [T3 EQ]. exists T3. subst T2. traceEq.
Qed.

Definition trace_intact (tr: trace): Prop := ~In Event_pterm tr.

Lemma trace_intact_E0 : trace_intact E0.
Proof. ii. ss. Qed.

Lemma trace_intact_app t0 t1
    (INTACT0: trace_intact t0)
    (INTACT1: trace_intact t1) :
  <<INTACT: trace_intact (t0 ** t1)>>.
Proof. ii. unfold trace_intact in *. rewrite in_app_iff in *. tauto. Qed.

Lemma trace_intact_app_rev t0 t1
    (INTACT: trace_intact (t0 ** t1)) :
  <<INTACT0: trace_intact t0>> /\ <<INTACT1: trace_intact t1>>.
Proof.
  ginduction t0; ss; i; split; auto; [ii; inv H | |].
  - ii. apply INTACT. apply in_app_iff. ss. des; auto.
  - ii. apply INTACT. apply in_app_iff. auto.
Qed.

Fixpoint trace_cut_pterm (tr: trace): trace :=
  match tr with
  | nil => nil
  | Event_pterm :: _ => nil
  | hd :: tl => hd :: (trace_cut_pterm tl)
  end.

Lemma trace_cut_pterm_intact t : trace_intact (trace_cut_pterm t).
Proof. ginduction t; ss. des_ifs; ii; ss; des; clarify. Qed.    

Lemma trace_cut_pterm_intact_app t0 t1
    (INTACT: trace_intact t0) :
  trace_cut_pterm (t0 ** t1) = t0 ** trace_cut_pterm t1.
Proof.
  ginduction t0; ss. i. Transparent Eapp. ss. rewrite IHt0.
  - unfold trace_intact in INTACT. ss.
    apply Classical_Prop.not_or_and in INTACT. des. destruct a; ss.
  - ii. apply INTACT. ss. auto.
Qed.    

Lemma trace_cut_pterm_pterm_app t0 t1
    (PTERM: ~ trace_intact t0) :
  trace_cut_pterm (t0 ** t1) = trace_cut_pterm t0.
Proof.
  ginduction t0; ss. i.
  - exfalso. apply PTERM. ii. ss.
  - i. unfold trace_intact in PTERM. apply Classical_Prop.NNPP in PTERM.
    ss. des; subst; auto. rewrite IHt0; auto.
Qed.

Lemma trace_cut_pterm_split t : exists t1, t = trace_cut_pterm t ** t1.
Proof.
  ginduction t; ss; eauto. des.
  exists (match a with | Event_pterm => a :: t | _ => t1 end).
  des_ifs; ss; f_equal; auto.
Qed.

Opaque Eapp.

(** * Relating values and event values *)

Set Implicit Arguments.

Section EVENTVAL.

(** Symbol environment used to translate between global variable names and their block identifiers. *)
Variable ge: Senv.t.

(** Translation between values and event values. *)

Inductive eventval_match: eventval -> typ -> val -> Prop :=
  | ev_match_int: forall i,
      eventval_match (EVint i) Tint (Vint i)
  | ev_match_long: forall i,
      eventval_match (EVlong i) Tlong (Vlong i)
  | ev_match_float: forall f,
      eventval_match (EVfloat f) Tfloat (Vfloat f)
  | ev_match_single: forall f,
      eventval_match (EVsingle f) Tsingle (Vsingle f)
  | ev_match_ptr: forall id b ofs,
      Senv.public_symbol ge id = true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match (EVptr_global id ofs) Tptr (Vptr b ofs).

Inductive eventval_list_match: list eventval -> list typ -> list val -> Prop :=
  | evl_match_nil:
      eventval_list_match nil nil nil
  | evl_match_cons:
      forall ev1 evl ty1 tyl v1 vl,
      eventval_match ev1 ty1 v1 ->
      eventval_list_match evl tyl vl ->
      eventval_list_match (ev1::evl) (ty1::tyl) (v1::vl).

(** Some properties of these translation predicates. *)

Lemma eventval_match_type:
  forall ev ty v,
  eventval_match ev ty v -> Val.has_type v ty.
Proof.
  intros. inv H; simpl; auto. unfold Tptr; destruct Archi.ptr64; auto.
Qed.

Lemma eventval_list_match_length:
  forall evl tyl vl, eventval_list_match evl tyl vl -> List.length vl = List.length tyl.
Proof.
  induction 1; simpl; eauto.
Qed.

Lemma eventval_match_lessdef:
  forall ev ty v1 v2,
  eventval_match ev ty v1 -> Val.lessdef v1 v2 -> eventval_match ev ty v2.
Proof.
  intros. inv H; inv H0; constructor; auto.
Qed.

Lemma eventval_list_match_lessdef:
  forall evl tyl vl1, eventval_list_match evl tyl vl1 ->
  forall vl2, Val.lessdef_list vl1 vl2 -> eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_lessdef; eauto. eauto.
Qed.

(** Determinism *)

Lemma eventval_match_determ_1:
  forall ev ty v1 v2, eventval_match ev ty v1 -> eventval_match ev ty v2 -> v1 = v2.
Proof.
  intros. inv H; inv H0; auto. congruence.
Qed.

Lemma eventval_match_determ_2:
  forall ev1 ev2 ty v, eventval_match ev1 ty v -> eventval_match ev2 ty v -> ev1 = ev2.
Proof.
  intros. inv H; inv H0; auto.
  decEq. eapply Senv.find_symbol_injective; eauto.
Qed.

Lemma eventval_list_match_determ_2:
  forall evl1 tyl vl, eventval_list_match evl1 tyl vl ->
  forall evl2, eventval_list_match evl2 tyl vl -> evl1 = evl2.
Proof.
  induction 1; intros. inv H. auto. inv H1. f_equal; eauto.
  eapply eventval_match_determ_2; eauto.
Qed.

(** Validity *)

Definition eventval_valid (ev: eventval) : Prop :=
  match ev with
  | EVint _ => True
  | EVlong _ => True
  | EVfloat _ => True
  | EVsingle _ => True
  | EVptr_global id ofs => Senv.public_symbol ge id = true
  end.

Definition eventval_type (ev: eventval) : typ :=
  match ev with
  | EVint _ => Tint
  | EVlong _ => Tlong
  | EVfloat _ => Tfloat
  | EVsingle _ => Tsingle
  | EVptr_global id ofs => Tptr
  end.

Lemma eventval_match_receptive:
  forall ev1 ty v1 ev2,
  eventval_match ev1 ty v1 ->
  eventval_valid ev1 -> eventval_valid ev2 -> eventval_type ev1 = eventval_type ev2 ->
  exists v2, eventval_match ev2 ty v2.
Proof.
  intros. unfold eventval_type, Tptr in H2. remember Archi.ptr64 as ptr64.
  inversion H; subst ev1 ty v1; clear H; destruct ev2; simpl in H2; inv H2.
- exists (Vint i0); constructor.
- simpl in H1; exploit Senv.public_symbol_exists; eauto. intros [b FS].
  exists (Vptr b i1); rewrite H3. constructor; auto.
- exists (Vlong i0); constructor.
- simpl in H1; exploit Senv.public_symbol_exists; eauto. intros [b FS].
  exists (Vptr b i1); rewrite H3; constructor; auto.
- exists (Vfloat f0); constructor.
- destruct Archi.ptr64; discriminate.
- exists (Vsingle f0); constructor; auto.
- destruct Archi.ptr64; discriminate.
- exists (Vint i); unfold Tptr; rewrite H5; constructor.
- exists (Vlong i); unfold Tptr; rewrite H5; constructor.
- destruct Archi.ptr64; discriminate.
- destruct Archi.ptr64; discriminate.
- exploit Senv.public_symbol_exists. eexact H1. intros [b' FS].
  exists (Vptr b' i0); constructor; auto.
Qed.

Lemma eventval_match_valid:
  forall ev ty v, eventval_match ev ty v -> eventval_valid ev.
Proof.
  destruct 1; simpl; auto.
Qed.

Lemma eventval_match_same_type:
  forall ev1 ty v1 ev2 v2,
  eventval_match ev1 ty v1 -> eventval_match ev2 ty v2 -> eventval_type ev1 = eventval_type ev2.
Proof.
  destruct 1; intros EV; inv EV; auto.
Qed.

End EVENTVAL.

(** Invariance under changes to the global environment *)

Section EVENTVAL_INV.

Variables ge1 ge2: Senv.t.

Hypothesis public_preserved:
  forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id.

Lemma eventval_valid_preserved:
  forall ev, eventval_valid ge1 ev -> eventval_valid ge2 ev.
Proof.
  intros. destruct ev; simpl in *; auto. rewrite <- H; auto.
Qed.

Hypothesis symbols_preserved:
  forall id, Senv.find_symbol ge2 id = Senv.find_symbol ge1 id.

Lemma eventval_match_preserved:
  forall ev ty v,
  eventval_match ge1 ev ty v -> eventval_match ge2 ev ty v.
Proof.
  induction 1; constructor; auto.
  rewrite public_preserved; auto.
  rewrite symbols_preserved; auto.
Qed.

Lemma eventval_list_match_preserved:
  forall evl tyl vl,
  eventval_list_match ge1 evl tyl vl -> eventval_list_match ge2 evl tyl vl.
Proof.
  induction 1; constructor; auto. eapply eventval_match_preserved; eauto.
Qed.

End EVENTVAL_INV.

(** Compatibility with memory injections *)

Section EVENTVAL_INJECT.

Variable f: block -> option (block * Z).
Variable ge1 ge2: Senv.t.

Definition symbols_inject : Prop :=
   (forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id)
/\ (forall id b1 b2 delta,
     f b1 = Some(b2, delta) -> Senv.find_symbol ge1 id = Some b1 ->
     delta = 0 /\ Senv.find_symbol ge2 id = Some b2)
/\ (forall id b1,
     Senv.public_symbol ge1 id = true -> Senv.find_symbol ge1 id = Some b1 ->
     exists b2, f b1 = Some(b2, 0) /\ Senv.find_symbol ge2 id = Some b2)
/\ (forall b1 b2 delta,
     f b1 = Some(b2, delta) ->
     Senv.block_is_volatile ge2 b2 = Senv.block_is_volatile ge1 b1).

Hypothesis symb_inj: symbols_inject.

Lemma eventval_match_inject:
  forall ev ty v1 v2,
  eventval_match ge1 ev ty v1 -> Val.inject f v1 v2 -> eventval_match ge2 ev ty v2.
Proof.
  intros. inv H; inv H0; try constructor; auto.
  destruct symb_inj as (A & B & C & D). exploit C; eauto. intros [b3 [EQ FS]]. rewrite H4 in EQ; inv EQ.
  rewrite Ptrofs.add_zero. constructor; auto. rewrite A; auto.
Qed.

Lemma eventval_match_inject_2:
  forall ev ty v1,
  eventval_match ge1 ev ty v1 ->
  exists v2, eventval_match ge2 ev ty v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H; try (econstructor; split; eauto; constructor; fail).
  destruct symb_inj as (A & B & C & D). exploit C; eauto. intros [b2 [EQ FS]].
  exists (Vptr b2 ofs); split. econstructor; eauto.
  econstructor; eauto. rewrite Ptrofs.add_zero; auto.
Qed.

Lemma eventval_list_match_inject:
  forall evl tyl vl1, eventval_list_match ge1 evl tyl vl1 ->
  forall vl2, Val.inject_list f vl1 vl2 -> eventval_list_match ge2 evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_inject; eauto. eauto.
Qed.

End EVENTVAL_INJECT.

(* gm is concrete memory map(mem_concrete) of some memory *)

Definition to_int_ev (id: ident) (ofs: ptrofs) (gm: ident -> option Z) : option val :=
  match gm id with
  | Some addr => Some (if Archi.ptr64 then Vlong (Int64.repr (addr + Ptrofs.unsigned ofs)) else Vint (Int.repr (addr + Ptrofs.unsigned ofs)))
  | _ => None
  end.

Section EVENTVAL_BIND.

(* Variable ge: Senv.t. *)
Variable gm: ident -> option Z.

Definition eventval_bind (e1 e2: eventval) : Prop :=
  match e1, e2 with
  | EVptr_global id ofs, EVint i =>
      <<SF: Archi.ptr64 = false>> /\
      <<TOINT: to_int_ev id ofs gm = Some (Vint i)>>
  | EVptr_global id ofs, EVlong i =>
      <<SF: Archi.ptr64 = true>> /\
      <<TOINT: to_int_ev id ofs gm = Some (Vlong i)>>
  | _, _ => e1 = e2
  end.

Lemma eventval_bind_refl ev:
  eventval_bind ev ev.
Proof. destruct ev; ss. Qed.

End EVENTVAL_BIND.

(* m: current memory, gm: snap shot of concrete part of init state  *)
Definition ge_binded (ge:Senv.t) (m: mem) (gm: ident -> option Z) :=
    forall id, Senv.public_symbol ge id = true ->
    forall b, Senv.find_symbol ge id = Some b ->
         Maps.PTree.get b (Mem.mem_concrete m) = gm id
         /\
         exists addr, gm id = Some addr.

Section EVENT_REL.

Definition event_rel (evval_rel: eventval -> eventval -> Prop) (e1 e2: event) : Prop :=
  match e1, e2 with
  | Event_syscall st1 args1 res1, Event_syscall st2 args2 res2 =>
      <<ST: st1 = st2>> /\
      <<ARGS: Forall2 evval_rel args1 args2>> /\
      <<RES: evval_rel res1 res2>>
  | Event_vload chunk1 id1 ofs1 res1, Event_vload chunk2 id2 ofs2 res2 =>
      <<CHUNK: chunk1 = chunk2>> /\
      <<ID: id1 = id2>> /\
      <<OFS: ofs1 = ofs2>> /\
      <<RES: evval_rel res1 res2>>
  | Event_vstore chunk1 id1 ofs1 arg1, Event_vstore chunk2 id2 ofs2 arg2 =>
      <<CHUNK: chunk1 = chunk2>> /\
      <<ID: id1 = id2>> /\
      <<OFS: ofs1 = ofs2>> /\
      <<ARG: evval_rel arg1 arg2>>
  | Event_annot id1 args1, Event_annot id2 args2 =>
      <<ID: id1 = id2>> /\
      <<ARGS: Forall2 evval_rel args1 args2>>
  | _, _ => e1 = e2
  end.

Definition tr_rel (ev_rel: event -> event -> Prop) (tr1 tr2: trace) : Prop :=
  Forall2 ev_rel tr1 tr2.

Definition evval_rel (gvmap: ident -> option Z) : eventval -> eventval -> Prop := eventval_bind gvmap.
Definition ev_rel (gvmap: ident -> option Z) : event -> event -> Prop := event_rel (evval_rel gvmap).

Lemma eventval_list_eq (ev1 ev2: list eventval)
  (EQ: Forall2 eq ev1 ev2) : ev1 = ev2.
Proof. ginduction EQ; ss. subst; eauto. Qed.

Lemma tr_rel_eq tr1 tr2
  (EQ: tr_rel eq tr1 tr2): tr1 = tr2.
Proof. ginduction EQ; ss. subst. eauto. Qed.

End EVENT_REL.

Lemma evval_rel_refl pm ev: evval_rel pm ev ev.
Proof. destruct ev; ss. Qed.

Lemma evval_list_rel_refl pm ev: Forall2 (evval_rel pm) ev ev.
Proof. ginduction ev; ss. econs; eauto. eapply evval_rel_refl. Qed.

Lemma ev_rel_refl pm ev: ev_rel pm ev ev.
Proof.
  destruct ev; ss; esplits; eauto.
  - eapply evval_list_rel_refl.
  - eapply evval_rel_refl.
  - eapply evval_rel_refl.
  - eapply evval_rel_refl.
  - eapply evval_list_rel_refl.
Qed.

Lemma tr_rel_refl ev_rel
    (REFL: forall ev, ev_rel ev ev: Prop) tr:
  tr_rel ev_rel tr tr.
Proof. induction tr; ss; ii; econs; eauto. Qed.

Lemma tr_rel_app
    ev_rel tr1 tr1' tr2 tr2'
    (TR1: tr_rel ev_rel tr1 tr1')
    (TR2: tr_rel ev_rel tr2 tr2') :
  tr_rel ev_rel (tr1 ** tr2) (tr1' ** tr2').
Proof. eapply Forall2_app; eauto. Qed.

Lemma eventval_match_binded
    (ge: Senv.t) ev1 ty m v1 v2 gm
    (GB: ge_binded ge m gm)
    (EM: eventval_match ge ev1 ty v1)
    (BIND: val_intptr m v1 v2):
  exists ev2, eventval_match ge ev2 ty v2 /\ evval_rel gm ev1 ev2.
Proof.
  inv EM; inv BIND; try by (esplits; eauto; econs); des_ifs. ss.
  ss. des_ifs_safe. unfold Mem.ptr2int in Heq. des_ifs.
  exploit GB; eauto. i. des. esplits; [econs|].
  ss. esplits; eauto. unfold to_int_ev. rewrite H2. des_ifs.
  rewrite H1 in Heq0. clarify.
Qed.

Lemma eventval_list_match_binded
    (ge: Senv.t) evl1 tyl m vl1 vl2 gm
    (GB: ge_binded ge m gm)
    (EM: eventval_list_match ge evl1 tyl vl1)
    (BIND: val_intptrist m vl1 vl2):
  exists evl2, eventval_list_match ge evl2 tyl vl2 /\ Forall2 (evval_rel gm) evl1 evl2.
Proof.
  ginduction EM; ii; [inv BIND; esplits; eauto; econs|].
  inv BIND. hexploit IHEM; eauto. i. des. hexploit eventval_match_binded; eauto. i. des.
  esplits; eauto. econs; eauto.
Qed.


(** * Matching traces. *)

Section MATCH_TRACES.

Variable ge: Senv.t.

(** Matching between traces corresponding to single transitions.
  Arguments (provided by the program) must be equal.
  Results (provided by the outside world) can vary as long as they
  can be converted safely to values. *)

Inductive match_traces: trace -> trace -> Prop :=
  | match_traces_E0:
      match_traces nil nil
  | match_traces_syscall: forall id args res1 res2,
      eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 ->
      match_traces (Event_syscall id args res1 :: nil) (Event_syscall id args res2 :: nil)
  | match_traces_vload: forall chunk id ofs res1 res2,
      eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 ->
      match_traces (Event_vload chunk id ofs res1 :: nil) (Event_vload chunk id ofs res2 :: nil)
  | match_traces_vstore: forall chunk id ofs arg,
      match_traces (Event_vstore chunk id ofs arg :: nil) (Event_vstore chunk id ofs arg :: nil)
  | match_traces_annot: forall id args,
      match_traces (Event_annot id args :: nil) (Event_annot id args :: nil).

End MATCH_TRACES.

(** Invariance by change of global environment *)

Section MATCH_TRACES_INV.

Variables ge1 ge2: Senv.t.

Hypothesis public_preserved:
  forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id.

Lemma match_traces_preserved:
  forall t1 t2, match_traces ge1 t1 t2 -> match_traces ge2 t1 t2.
Proof.
  induction 1; constructor; auto; eapply eventval_valid_preserved; eauto.
Qed.

End MATCH_TRACES_INV.

(** An output trace is a trace composed only of output events,
  that is, events that do not take any result from the outside world. *)

Definition output_event (ev: event) : Prop :=
  match ev with
  | Event_pterm => True
  | Event_syscall _ _ _ => False
  | Event_vload _ _ _ _ => False
  | Event_vstore _ _ _ _ => True
  | Event_annot _ _ => True
  end.

Fixpoint output_trace (t: trace) : Prop :=
  match t with
  | nil => True
  | ev :: t' => output_event ev /\ output_trace t'
  end.

(** * Semantics of volatile memory accesses *)

Inductive volatile_load (ge: Senv.t):
                   memory_chunk -> mem -> block -> ptrofs -> trace -> val -> Prop :=
  | volatile_load_vol: forall chunk m b ofs id ev v (VLPERM: Mem.perm m b (Ptrofs.unsigned ofs) Cur Nonempty),
      Senv.block_is_volatile ge b = true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match ge ev (type_of_chunk chunk) v ->
      volatile_load ge chunk m b ofs
                      (Event_vload chunk id ofs ev :: nil)
                      (Val.load_result chunk v)
  | volatile_load_nonvol: forall chunk m b ofs v,
      Senv.block_is_volatile ge b = false ->
      Mem.load chunk m b (Ptrofs.unsigned ofs) = Some v ->
      volatile_load ge chunk m b ofs E0 v.

Inductive volatile_store (ge: Senv.t):
                  memory_chunk -> mem -> block -> ptrofs -> val -> trace -> mem -> Prop :=
  | volatile_store_vol: forall chunk m b ofs id ev v (VLPERM: Mem.perm m b (Ptrofs.unsigned ofs) Cur Nonempty),
      Senv.block_is_volatile ge b = true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match ge ev (type_of_chunk chunk) (Val.load_result chunk v) ->
      volatile_store ge chunk m b ofs v
                      (Event_vstore chunk id ofs ev :: nil)
                      m
  | volatile_store_nonvol: forall chunk m b ofs v m',
      Senv.block_is_volatile ge b = false ->
      Mem.store chunk m b (Ptrofs.unsigned ofs) v = Some m' ->
      volatile_store ge chunk m b ofs v E0 m'.

(** * Semantics of external functions *)

(** For each external function, its behavior is defined by a predicate relating:
- the global symbol environment
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).
*)

Definition extcall_sem : Type :=
  Senv.t -> list val -> mem -> trace -> val -> mem -> Prop.

(** We now specify the expected properties of this predicate. *)

Definition loc_out_of_bounds (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Nonempty.

Definition loc_not_writable (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Writable.

Definition loc_unmapped (f: meminj) (b: block) (ofs: Z): Prop :=
  f b = None.

Definition loc_out_of_reach (f: meminj) (m: mem) (b: block) (ofs: Z): Prop :=
  forall b0 delta,
  f b0 = Some(b, delta) -> ~Mem.perm m b0 (ofs - delta) Max Nonempty.

Definition inject_separated (f f': meminj) (m1 m2: mem): Prop :=
  forall b1 b2 delta,
  f b1 = None -> f' b1 = Some(b2, delta) ->
  ~Mem.valid_block m1 b1 /\ ~Mem.valid_block m2 b2.

Definition nonempty_perm (m: mem) (b: block) (ofs: Z) :=
  Mem.perm m b ofs Max Nonempty
  /\ (forall k p, Mem.perm m b ofs k p -> p = Nonempty).

Definition self_inj (f:meminj) : Prop :=
  forall b b' delta, f b = Some (b', delta) -> b = b' /\ delta = 0.

Record extcall_properties_common (sem: extcall_sem) (sg: signature) : Prop :=
  mk_extcall_properties_common {
  
(** The return value of an external call must agree with its signature. *)
  ec_well_typed:
    forall ge vargs m1 t vres m2,
    sem ge vargs m1 t vres m2 ->
    Val.has_rettype vres sg.(sig_res);

(** The semantics is invariant under change of global environment that preserves symbols. *)
  ec_symbols_preserved:
    forall ge1 ge2 vargs m1 t vres m2,
    Senv.equiv ge1 ge2 ->
    sem ge1 vargs m1 t vres m2 ->
    sem ge2 vargs m1 t vres m2;

(** External calls cannot invalidate memory blocks.  (Remember that
  freeing a block does not invalidate its block identifier.) *)
  ec_valid_block:
    forall ge vargs m1 t vres m2 b,
    sem ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.valid_block m2 b;

(** External calls cannot increase the max permissions of a valid block.
    They can decrease the max permissions, e.g. by freeing. *)
  ec_max_perm:
    forall ge vargs m1 t vres m2 b ofs p,
    sem ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p;

(** External call cannot modify memory unless they have [Max, Writable]
   permissions. *)
  ec_readonly:
    forall ge vargs m1 t vres m2 b ofs n bytes,
    sem ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b ->
    Mem.loadbytes m2 b ofs n = Some bytes ->
    (forall i, ofs <= i < ofs + n -> ~Mem.perm m1 b i Max Writable) ->
    Mem.loadbytes m1 b ofs n = Some bytes;

  ec_binds:
    forall ge vargs m1 t vres m2,
    sem ge vargs m1 t vres m2 ->
    (forall b caddr, Maps.PTree.get b m1.(Mem.mem_concrete) = Some caddr -> Maps.PTree.get b m2.(Mem.mem_concrete) = Some caddr);

  ec_nonempty:
    forall ge vargs m1 t vres m2,
    sem ge vargs m1 t vres m2 -> (forall b ofs, nonempty_perm m1 b ofs -> nonempty_perm m2 b ofs);    
}.

(* backward version of extcall properties *)
Record extcall_properties_backward (sem: extcall_sem) (sg: signature) : Prop :=
  mk_extcall_properties_backward {

  ec_properties_backward_common:
    extcall_properties_common sem sg;

(** External calls must commute with memory extensions, in the
  following sense. *)
  ec_mem_extends_backward
      ge vargs m1 t vres' m2' m1' vargs'
      (CALLTGT: sem ge vargs' m1' t vres' m2')
      (MEM: Mem.extends m1 m1')
      (ARGS: Val.lessdef_list vargs vargs') :
    (exists vres m2,
      <<CALLSRC: sem ge vargs m1 t vres m2>>
    /\ <<RETV: Val.lessdef vres vres'>>
    /\ <<MEM: Mem.extends m2 m2'>>
    /\ <<PRIV: Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'>>)
    \/ <<UBSRC: (forall t' vres m2, ~ sem ge vargs m1 t' vres m2)>>
    \/ (<<PTERM: ~trace_intact t >> /\
       exists t' vres1 m21, <<CALLSRC: sem ge vargs m1 t' vres1 m21>> /\
                       <<SUB: exists tl, t' = (trace_cut_pterm t) ** tl>>);

  ec_mem_extends_backward_progress
      ge vargs m1 t vres m2 m1' vargs'
      (CALLSRC: sem ge vargs m1 t vres m2)
      (MEM: Mem.extends m1 m1')
      (ARGS: Val.lessdef_list vargs vargs') :
    (exists t' vres' m2', <<CALLTGT: sem ge vargs' m1' t' vres' m2'>>);

(** External calls must commute with memory injections,
  in the following sense. *)
  ec_mem_inject_backward
      ge1 ge2 vargs m1 t vres' m2' f m1' vargs'
      (SYMB: symbols_inject f ge1 ge2)
      (CALLTGT: sem ge2 vargs' m1' t vres' m2')
      (MEM: Mem.inject f m1 m1')
      (ARGS: Val.inject_list f vargs vargs') :
    (exists f' vres m2,
      <<CALLSRC: sem ge1 vargs m1 t vres m2>>
    /\ <<RETV: Val.inject f' vres vres'>>
    /\ <<MEM: Mem.inject f' m2 m2'>>
    /\ <<MEMPRIVSRC: Mem.unchanged_on (loc_unmapped f) m1 m2>>
    /\ <<MEMPRIVTGT: Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'>>
    /\ <<INJINCR: inject_incr f f'>>
    /\ <<INJSEP: inject_separated f f' m1 m1'>>)
    \/ <<UBSRC: (forall t' vres m2, ~ sem ge1 vargs m1 t' vres m2)>>
    \/ (<<PTERM: ~trace_intact t >> /\
       exists t' vres1 m21, <<CALLSRC: sem ge1 vargs m1 t' vres1 m21>> /\
                       <<SUB: exists tl, t' = (trace_cut_pterm t) ** tl>>);

  ec_mem_inject_backward_progress
      ge1 ge2 vargs m1 t vres m2 f m1' vargs'
      (SYMB: symbols_inject f ge1 ge2)
      (CALLSRC: sem ge1 vargs m1 t vres m2)
      (MEM: Mem.inject f m1 m1')
      (ARGS: Val.inject_list f vargs vargs') :
    (exists t'' vres' m2', <<CALLTGT: sem ge2 vargs' m1' t'' vres' m2'>>);

  ec_sound
      ge vargs m1 m2 t vres f
      (SELF: self_inj f)
      (SYMB: symbols_inject f ge ge)
      (CALLSRC: sem ge vargs m1 t vres m2)
      (MEM: Mem.inject f m1 m1)
      (ARGS: Val.inject_list f vargs vargs) :
    (exists f',
      <<RETV: Val.inject f' vres vres>>
    /\ <<MEM: Mem.inject f' m2 m2>>
    /\ <<MEMPRIVSRC: Mem.unchanged_on (loc_unmapped f) m1 m2>>
    /\ <<MEMPRIVTGT: Mem.unchanged_on (loc_out_of_reach f m1) m1 m2>>
    /\ <<INJINCR: inject_incr f f'>>
    /\ <<INJSEP: inject_separated f f' m1 m1>>);

   ec_concrete_extends_backward :
      forall ge vargs m1 t' vres' m2' m1' vargs' gm (TINIT: ge_binded ge m1' gm),
      sem ge vargs' m1' t' vres' m2' -> concrete_extends m1 m1' ->
      val_intptrist m1' vargs vargs' ->
    (exists t vres m2,
      <<TRREL: tr_rel (ev_rel gm) t t'>>
    /\ <<CALLSRC: sem ge vargs m1 t vres m2>>
    /\ <<RETV: val_intptr m2' vres vres'>>
    /\ <<MEM: concrete_extends m2 m2'>>
    /\ <<PRIV: Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'>>)
    \/ <<UBSRC: (forall t vres m2, ~ sem ge vargs m1 t vres m2)>>
    \/ (<<PTERM: ~ trace_intact t' >> /\
       exists t vres1 m21, <<CALLSRC: sem ge vargs m1 t vres1 m21>> /\
                      <<SUB: exists tl, tr_rel (ev_rel gm) t (Eapp (trace_cut_pterm t') tl)>>);

  ec_concrete_extends_backward_progress
      ge vargs m1 t vres m2 m1' vargs' gm
      (TINIT: ge_binded ge m1' gm)
      (CALLSRC: sem ge vargs m1 t vres m2)
      (MEM: concrete_extends m1 m1')
      (ARGS: val_intptrist m1' vargs vargs') :
    (exists t'' vres' m2', <<CALLTGT: sem ge vargs' m1' t'' vres' m2'>>);

}.

(* forward version of extcall properties *)
Record extcall_properties (sem: extcall_sem) (sg: signature) : Prop :=
  mk_extcall_properties {

  ec_properties_common:
    extcall_properties_common sem sg;

(** External calls produce at most one event. *)
  ec_trace_length:
    forall ge vargs m t vres m',
    sem ge vargs m t vres m' -> (length t <= 1)%nat;
      
(** External calls must commute with memory extensions, in the
  following sense. *)
  ec_mem_extends:
    forall ge vargs m1 t vres m2 m1' vargs',
    sem ge vargs m1 t vres m2 ->
    Mem.extends m1 m1' ->
    Val.lessdef_list vargs vargs' ->
    exists vres', exists m2',
       sem ge vargs' m1' t vres' m2'
    /\ Val.lessdef vres vres'
    /\ Mem.extends m2 m2'
    /\ Mem.unchanged_on (loc_out_of_bounds m1) m1' m2';

(** External calls must commute with memory injections,
  in the following sense. *)
  ec_mem_inject:
    forall ge1 ge2 vargs m1 t vres m2 f m1' vargs',
    symbols_inject f ge1 ge2 ->
    sem ge1 vargs m1 t vres m2 ->
    Mem.inject f m1 m1' ->
    Val.inject_list f vargs vargs' ->
    exists f', exists vres', exists m2',
       sem ge2 vargs' m1' t vres' m2'
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1';

  ec_mem_concrete_extends:
    forall ge vargs m1 t vres m2 m1' vargs' gm (TINIT: ge_binded ge m1' gm),
    sem ge vargs m1 t vres m2 ->
    concrete_extends m1 m1' ->
    val_intptrist m1' vargs vargs' ->
    exists t', exists vres', exists m2',
      tr_rel (ev_rel gm) t t' 
    /\ sem ge vargs' m1' t' vres' m2'
    /\ val_intptr m2' vres vres'
    /\ concrete_extends m2 m2'
    /\ Mem.unchanged_on (loc_out_of_bounds m1) m1' m2';

(** External calls must be receptive to changes of traces by another, matching trace. *)
  ec_receptive:
    forall ge vargs m t1 vres1 m1 t2,
    sem ge vargs m t1 vres1 m1 -> match_traces ge t1 t2 ->
    exists vres2, exists m2, sem ge vargs m t2 vres2 m2;

(** External calls must be deterministic up to matching between traces. *)
  ec_determ:
    forall ge vargs m t1 vres1 m1 t2 vres2 m2,
    sem ge vargs m t1 vres1 m1 -> sem ge vargs m t2 vres2 m2 ->
    t1 = t2 /\ vres1 = vres2 /\ m1 = m2;

  ec_binds_rev:
    forall ge vargs m1 t vres m2,
    sem ge vargs m1 t vres m2 ->
    (forall b caddr, Maps.PTree.get b m2.(Mem.mem_concrete) = Some caddr -> Maps.PTree.get b m1.(Mem.mem_concrete) = Some caddr);

}.

(** ** Semantics of volatile loads *)

Inductive volatile_load_sem (chunk: memory_chunk) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_load_sem_intro: forall b ofs m t v addr (TOPTR: Mem.to_ptr addr m = Some (Vptr b ofs)),
      volatile_load ge chunk m b ofs t v ->
      volatile_load_sem chunk ge (addr :: nil) m t v m.

Lemma volatile_load_preserved:
  forall ge1 ge2 chunk m b ofs t v,
  Senv.equiv ge1 ge2 ->
  volatile_load ge1 chunk m b ofs t v ->
  volatile_load ge2 chunk m b ofs t v.
Proof.
  intros. destruct H as (A & B & C). inv H0; constructor; auto.
  rewrite C; auto.
  rewrite A; auto.
  eapply eventval_match_preserved; eauto.
  rewrite C; auto.
Qed.

Lemma volatile_load_extends:
  forall ge chunk m b ofs t v m',
  volatile_load ge chunk m b ofs t v ->
  Mem.extends m m' ->
  exists v', volatile_load ge chunk m' b ofs t v' /\ Val.lessdef v v'.
Proof.
  intros. inv H.
  econstructor; split; eauto. econstructor; eauto.
  eapply Mem.perm_extends; eauto.
  exploit Mem.load_extends; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
Qed.

Lemma volatile_load_concrete_extends:
  forall ge chunk m b ofs t v m',
  volatile_load ge chunk m b ofs t v ->
  concrete_extends m m' ->
  exists v', volatile_load ge chunk m' b ofs t v' /\ val_intptr m' v v'.
Proof.
  intros. inv H.
  econstructor; split; eauto. econstructor; eauto.
  eapply concrete_extends_perm_implies; eauto.
  eapply val_intptr_refl.
  exploit load_concrete_extends; eauto. i. des.
  esplits; eauto. econs; eauto.
Qed.

Lemma volatile_load_inject:
  forall ge1 ge2 f chunk m b ofs t v b' ofs' m',
  symbols_inject f ge1 ge2 ->
  volatile_load ge1 chunk m b ofs t v ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  Mem.inject f m m' ->
  exists v', volatile_load ge2 chunk m' b' ofs' t v' /\ Val.inject f v v'.
Proof.
  intros until m'; intros SI VL VI MI. generalize SI; intros (A & B & C & D).
  inv VL.
- (* volatile load *)
  inv VI. exploit B; eauto. intros [U V]. subst delta.
  exploit eventval_match_inject_2; eauto. intros (v2 & X & Y).
  rewrite Ptrofs.add_zero. exists (Val.load_result chunk v2); split.
  constructor; auto.
  exploit Mem.perm_inject; eauto. ii.
  assert (Ptrofs.unsigned ofs + 0 = Ptrofs.unsigned ofs) by lia.
  rewrite H3 in H2. eauto.
  erewrite D; eauto.
  apply Val.load_result_inject. auto.
- (* normal load *)
  exploit Mem.loadv_inject; eauto. unfold Mem.loadv. ss. simpl; eauto. simpl; intros (v2 & X & Y).
  exists v2; split; auto.
  constructor; auto.
  inv VI. erewrite D; eauto.
Qed.

Lemma volatile_load_receptive:
  forall ge chunk m b ofs t1 t2 v1,
  volatile_load ge chunk m b ofs t1 v1 -> match_traces ge t1 t2 ->
  exists v2, volatile_load ge chunk m b ofs t2 v2.
Proof.
  intros. inv H; inv H0.
  exploit eventval_match_receptive; eauto. intros [v' EM].
  exists (Val.load_result chunk v'). constructor; auto.
  exists v1; constructor; auto.
Qed.

Lemma volatile_load_perm ge chunk m b ofs t v
    (VL: volatile_load ge chunk m b ofs t v):
  <<PERM: Mem.perm m b (Ptrofs.unsigned ofs) Cur Nonempty>>.
Proof.
  inv VL; ss. exploit Mem.load_valid_access; eauto. i. inv H1.
  r in H2. specialize (H2 (Ptrofs.unsigned ofs)).
  exploit H2; eauto; [destruct chunk; ss; lia|]. i.
  eapply Mem.perm_implies; eauto. eapply perm_any_N.
Qed.

Lemma volatile_load_extends_backward
    ge chunk m b ofs t v' m'
    (VLOADTGT: volatile_load ge chunk m' b ofs t v')
    (MEXT: Mem.extends m m') :
  (exists v, <<VLOADSRC: volatile_load ge chunk m b ofs t v>> /\ <<VLD: Val.lessdef v v'>>)
  \/ (<<VLOADFAIL: forall t v, ~ volatile_load ge chunk m b ofs t v>>).
Proof.
  ii. inv VLOADTGT.
  - destruct (classic (Mem.perm m b (Ptrofs.unsigned ofs) Cur Nonempty)).
    + left. esplits;[econs; eauto| eauto].
    + right. ii. eapply H2. eapply volatile_load_perm; eauto.
  - exploit Mem.load_extends_backward; eauto. ii. des.
    { left. esplits; eauto. econs 2; eauto. }
    { right. ii. inv H1; clarify. }
Qed.

Lemma volatile_load_concrete_extends_backward
    ge chunk m b ofs t' v' m'
    (VLOADTGT: volatile_load ge chunk m' b ofs t' v')
    (MEXT: concrete_extends m m') :
  (exists v, <<VLOADSRC: volatile_load ge chunk m b ofs t' v>> /\ <<VLD: val_intptr m' v v'>>)
  \/ (<<VLOADFAIL: forall t v, ~ volatile_load ge chunk m b ofs t v>>).
Proof.
  ii. inv VLOADTGT.
  - destruct (classic (Mem.perm m b (Ptrofs.unsigned ofs) Cur Nonempty)).
    2:{ right. ii. eapply H2. eapply volatile_load_perm; eauto. }
    left. esplits; eauto; [econs; eauto| eapply val_intptr_refl].
  - destruct (Mem.load chunk m b (Ptrofs.unsigned ofs)) eqn:LD1.
    2:{ right. ii. inv H1; clarify. }
    exploit load_concrete_extends; eauto. ii. des.
    clarify. left. esplits; eauto. econs 2; eauto.
Qed.

Lemma volatile_load_extends_fail ge chunk m b ofs m'
    (FAILTGT: forall t v', ~volatile_load ge chunk m' b ofs t v')
    (MEXT: Mem.extends m m') :
  (<<FAILSRC: forall t v, ~ volatile_load ge chunk m b ofs t v>>).
Proof.
  ii. exploit volatile_load_extends; eauto. ii. des. eapply FAILTGT in H0. clarify.
Qed.

Lemma volatile_load_inject_backward
    ge1 ge2 f chunk m b ofs t v' b' ofs' m'
    (SI: symbols_inject f ge1 ge2)
    (VLOADTGT: volatile_load ge2 chunk m' b' ofs' t v')
    (VI: Val.inject f (Vptr b ofs) (Vptr b' ofs'))
    (MI: Mem.inject f m m') :
  (exists v, <<VLOADSRC: volatile_load ge1 chunk m b ofs t v>> /\ <<VI': Val.inject f v v'>>)
  \/ (<<VLOADFAIL: forall t v, ~ volatile_load ge1 chunk m b ofs t v>>).
Proof.
  generalize SI; intros (A & B & C & D). inv VLOADTGT.
(* volatile load *)
- inv VI.
  assert (Senv.block_is_volatile ge1 b = true).
  { erewrite <- D; eauto. }
  destruct (Senv.find_symbol ge1 id) eqn: SYMB.
  2: { right. ii. inv H3; clarify.
       exploit B; eauto. i. des. subst.
       exploit Senv.find_symbol_injective; [eapply H8|eapply H0|].
       i. des. subst. clarify. }
  destruct (peq b0 b) eqn: BLK.
  2: { right. ii. inv H3; clarify.
       exploit B; eauto. i. des. subst.
       exploit Senv.find_symbol_injective; [eapply H8|eapply H0|].
       i. des. subst. clarify. }
  subst. clear BLK.
  (* make eventval_match ge2 ev (type_of_chunk chunk) v1 /\ Val.inject f v1 v *)
  assert (exists v1, eventval_match ge1 ev (type_of_chunk chunk) v1 /\ Val.inject f v1 v).
  { inv H1; try by (esplits; econs; econs).
    - assert (Senv.public_symbol ge1 id0 = true).
      { rewrite <- A; eauto. }
      exploit Senv.public_symbol_exists; eauto. i. des.
      exploit C; eauto. i. des; subst. clarify.
      exists (Vptr b1 ofs0). split; econs; eauto. rewrite Ptrofs.add_zero; eauto. }
  des. exploit B; eauto. i. des; subst.
  rewrite Ptrofs.add_zero.
  destruct (classic (Mem.perm m b (Ptrofs.unsigned ofs) Cur Nonempty)); cycle 1.
  { right. ii. eapply H6. eapply volatile_load_perm; eauto. }
  left. esplits. econs; eauto.
  apply Val.load_result_inject. auto.
(* normal load *)
- exploit Mem.loadv_inject_backward; eauto.
  { unfold Mem.loadv. ss. eapply H0. }
  simpl; intros [[v2 [X Y]] | FAIL].
  2: { right. ii. inv H1; clarify.
       - inv VI. erewrite D in H; eauto. clarify.
       - rr in FAIL. unfold Mem.loadv in FAIL. ss. clarify. }
  left. esplits; eauto. econs 2; eauto.
  inv VI. erewrite <- D; eauto.
Qed.

Lemma volatile_load_inject_fail
    ge1 ge2 f chunk m b ofs b' ofs' m'
    (SI: symbols_inject f ge1 ge2)
    (FAILTGT: forall t v', ~ volatile_load ge2 chunk m' b' ofs' t v')
    (VI: Val.inject f (Vptr b ofs) (Vptr b' ofs'))
    (MI: Mem.inject f m m') :
  (<<FAILSRC: forall t v, ~ volatile_load ge1 chunk m b ofs t v>>).
Proof.
  ii. exploit volatile_load_inject; eauto. i. des. eapply FAILTGT in H0; eauto.
Qed.

Lemma volatile_load_ok:
  forall chunk,
  extcall_properties_backward (volatile_load_sem chunk)
                     (mksignature (Tptr :: nil) (rettype_of_chunk chunk) cc_default).
Proof.
  intros; constructor; intros.
  econs; i.
(* well typed *)
- inv H. inv H0. apply Val.load_result_rettype.
  eapply Mem.load_rettype; eauto.
(* symbols *)
- inv H0. econstructor. eauto. eapply volatile_load_preserved; eauto.
(* valid blocks *)
- inv H; auto.
(* max perms *)
- inv H; auto.
(* readonly *)
- inv H; auto.
(* (* trace length *) *)
(* - inv H. inv H0; simpl; lia. *)
- inv H; ss.
(* nonempty *)
- inv H; ss.
(* mem extends *)
- destruct (classic (exists t' vres m1', volatile_load_sem chunk ge vargs m1 t' vres m1')); cycle 1.
  { right. left. ii. eapply H; eauto. }
  des. inv H. inv ARGS. inv H4. exploit Mem.to_ptr_extends; try eapply TOPTR; eauto. ii. des.
  inv CALLTGT; clarify. exploit volatile_load_extends_backward; eauto. i. des.
  2:{ exfalso. eapply VLOADFAIL; eauto. }
  left. esplits; eauto; [econs; eauto|apply Mem.unchanged_on_refl].
(* mem extends progress *)
- inv ARGS. inv CALLSRC. inv H0; inv CALLSRC.
  exploit Mem.to_ptr_extends; try eapply TOPTR; eauto. ii. des.
  exploit volatile_load_extends; eauto. i. des.
  esplits. econs; eauto.
(* mem injects *)
- destruct (classic (exists t' vres m1', volatile_load_sem chunk ge1 vargs m1 t' vres m1')); cycle 1.
  { right. left. ii. eapply H. eauto. }
  des. inv H. inv ARGS. inv H4. exploit Mem.to_ptr_inject; try eapply TOPTR; eauto. ii. des.
  inv CALLTGT; clarify. exploit volatile_load_inject_backward; eauto. i. des.
  2:{ exfalso. eapply VLOADFAIL; eauto. }
  left. esplits; eauto.
  + econs; eauto.
  + apply Mem.unchanged_on_refl.
  + apply Mem.unchanged_on_refl.
  + ii; clarify.
(* mem inject progress *)
- inv ARGS. inv CALLSRC. inv H0; inv CALLSRC.
  exploit Mem.to_ptr_inject; try eapply TOPTR; eauto. ii. des.
  inversion VINJ; subst.
  exploit volatile_load_inject; eauto. i. des.
  esplits. econs; eauto.
(* self-sim *)
- inv CALLSRC. inv ARGS. inv H5.
  exploit Mem.to_ptr_inject; eauto. i. des. inversion VINJ; subst.
  exploit volatile_load_inject; eauto.
  i. des. clarify. exploit SELF; eauto. i. des; subst.
  rewrite H5 in *.
  assert (vres = v').
  { inv H; inv H0; ss; clarify.
    exploit eventval_match_determ_1. eapply H8. eapply H17. i. subst; eauto. }
  subst. esplits; eauto.
  + apply Mem.unchanged_on_refl.
  + apply Mem.unchanged_on_refl.
  + ii; clarify.
(* CE *)
- destruct (classic (exists t vres m1', volatile_load_sem chunk ge vargs m1 t vres m1')); cycle 1.
  { right. left. ii. eapply H2; eauto. }
  des. inv H2. inv H. inv H1. inv H8.
  assert (b = b0 /\ ofs = ofs0).
  { unfold Mem.to_ptr in *. des_ifs; try by inv H6.
    - inv H6. exploit denormalize_concrete_extends; eauto. i. des; clarify.
    - inv H6. ss. des_ifs.
      assert (PERM: Mem.perm m2' b (Ptrofs.unsigned ofs) Max Nonempty).
      { eapply concrete_extends_perm_implies; eauto. eapply Mem.perm_cur.
        inv H3; eauto. eapply Mem.load_valid_access in H1.
        eapply Mem.valid_access_perm; eauto. eapply Mem.valid_access_implies; eauto.
        eapply perm_any_N. }
      exploit Mem.ptr2int_to_denormalize_max; eauto.
      { eapply Ptrofs.unsigned_range_2. }
      i. erewrite Int64.unsigned_repr in Heq1; cycle 1.
      { eapply Mem.denormalize_info in H. des. esplits. lia.
        unfold Ptrofs.max_unsigned, Int64.max_unsigned in *. erewrite <- Ptrofs.modulus_eq64; eauto. lia. }
      des; clarify. erewrite Ptrofs.repr_unsigned. eauto. }
  des; subst.
  exploit volatile_load_concrete_extends_backward; try eapply H0. eauto. i. des; cycle 1.
  { right. left. ii. eapply VLOADFAIL. eauto. }
  left. esplits; eauto.
  { instantiate (1:= t'). eapply tr_rel_refl. eapply ev_rel_refl. }
  { econs. eauto. eauto. }
  apply Mem.unchanged_on_refl.
(* CE progress *)
- inv CALLSRC. inv ARGS. inv H4. dup H2. inv H2; ss.
  + des_ifs. exploit denormalize_concrete_extends; eauto. i.
    exploit volatile_load_concrete_extends; eauto. i. des.
    esplits. econs; eauto. ss. des_ifs.
  + clarify. exploit volatile_load_concrete_extends; eauto. i. des.
    esplits. econs; eauto. ss.
  + des_ifs. exploit volatile_load_concrete_extends; eauto. intros (v' & VL & BIND).
    exploit Mem.ptr2int_to_denormalize_max.
    { eauto. }
    { eapply Ptrofs.unsigned_range_2. }
    { eapply concrete_extends_perm_implies; eauto. eapply Mem.perm_cur.
      inv H; eauto. eapply Mem.load_valid_access in H3.
      eapply Mem.valid_access_perm; eauto. eapply Mem.valid_access_implies; eauto.
      eapply perm_any_N. }
    i. des. esplits. econs.
    { ss. erewrite Int64.unsigned_repr.
      { des_ifs_safe. eapply Int64.same_if_eq in Heq1. exfalso.
        eapply Mem.denormalize_info in Heq0. des.
        clear - CRANGE CRANGE0 Heq1.
        (* make lemma *)
        assert (Int64.eq (Int64.repr z) Int64.zero = false).
        { unfold Int64.eq. rewrite Int64.unsigned_repr.
          2:{ unfold Ptrofs.max_unsigned, Int64.max_unsigned in *. erewrite <- Ptrofs.modulus_eq64; eauto. lia. }
          rewrite Int64.unsigned_zero. des_ifs. }
        rewrite Heq1 in H. ss. }
      eapply Mem.denormalize_info in H2. des.
      unfold Ptrofs.max_unsigned, Int64.max_unsigned in *. erewrite <- Ptrofs.modulus_eq64; eauto. lia. } 
    erewrite Ptrofs.repr_unsigned. eauto.
Qed.

(** ** Semantics of volatile stores *)

Inductive volatile_store_sem (chunk: memory_chunk) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_store_sem_intro: forall b ofs m1 v t m2 addr (TOPTR: Mem.to_ptr addr m1 = Some (Vptr b ofs)),
      volatile_store ge chunk m1 b ofs v t m2 ->
      volatile_store_sem chunk ge (addr :: v :: nil) m1 t Vundef m2.

Lemma volatile_store_preserved:
  forall ge1 ge2 chunk m1 b ofs v t m2,
  Senv.equiv ge1 ge2 ->
  volatile_store ge1 chunk m1 b ofs v t m2 ->
  volatile_store ge2 chunk m1 b ofs v t m2.
Proof.
  intros. destruct H as (A & B & C). inv H0; constructor; auto.
  rewrite C; auto.
  rewrite A; auto.
  eapply eventval_match_preserved; eauto.
  rewrite C; auto.
Qed.

Lemma unchanged_on_readonly:
  forall m1 m2 b ofs n bytes,
  Mem.unchanged_on (loc_not_writable m1) m1 m2 ->
  Mem.valid_block m1 b ->
  Mem.loadbytes m2 b ofs n = Some bytes ->
  (forall i, ofs <= i < ofs + n -> ~Mem.perm m1 b i Max Writable) ->
  Mem.loadbytes m1 b ofs n = Some bytes.
Proof.
  intros.
  rewrite <- H1. symmetry.
  apply Mem.loadbytes_unchanged_on_1 with (P := loc_not_writable m1); auto.
Qed.

Lemma volatile_store_readonly:
  forall ge chunk1 m1 b1 ofs1 v t m2,
  volatile_store ge chunk1 m1 b1 ofs1 v t m2 ->
  Mem.unchanged_on (loc_not_writable m1) m1 m2.
Proof.
  intros. inv H.
- apply Mem.unchanged_on_refl.
- eapply Mem.store_unchanged_on; eauto.
  exploit Mem.store_valid_access_3; eauto. intros [P Q].
  intros. unfold loc_not_writable. red; intros. elim H2.
  apply Mem.perm_cur_max. apply P. auto.
Qed.

Lemma volatile_store_extends:
  forall ge chunk m1 b ofs v t m2 m1' v',
  volatile_store ge chunk m1 b ofs v t m2 ->
  Mem.extends m1 m1' ->
  Val.lessdef v v' ->
  exists m2',
     volatile_store ge chunk m1' b ofs v' t m2'
  /\ Mem.extends m2 m2'
  /\ Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'.
Proof.
  intros. inv H.
- econstructor; split. econstructor; eauto.
  { eapply Mem.perm_extends; eauto. }
  eapply eventval_match_lessdef; eauto. apply Val.load_result_lessdef; auto.
  auto with mem.
- exploit Mem.store_within_extends; eauto. intros [m2' [A B]].
  exists m2'; intuition.
+ econstructor; eauto.
+ eapply Mem.store_unchanged_on; eauto.
  unfold loc_out_of_bounds; intros.
  assert (Mem.perm m1 b i Max Nonempty).
  { apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
    exploit Mem.store_valid_access_3. eexact H3. intros [P Q]. eauto. }
  tauto.
Qed.

(* Lemma volatile_store_concrete_extends: *)
(*   forall ge chunk m1 b ofs v t m2 m1' v', *)
(*   volatile_store ge chunk m1 b ofs v t m2 -> *)
(*   concrete_extends m1 m1' -> *)
(*   val_intptr m1' v v' -> *)
(*   exists m2', *)
(*      volatile_store ge chunk m1' b ofs v' t m2' *)
(*   /\ concrete_extends m2 m2' *)
(*   /\ Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'. *)
(* Proof. *)
(*   intros. inv H. *)
(* - econstructor; split. econstructor; eauto. *)
(*   { eapply concrete_extends_perm; eauto. } *)
(*   eapply eventval_match_lessdef; eauto. apply Val.load_result_lessdef; auto. *)
(*   auto with mem. *)
(* - exploit Mem.store_within_extends; eauto. intros [m2' [A B]]. *)
(*   exists m2'; intuition. *)
(* + econstructor; eauto. *)
(* + eapply Mem.store_unchanged_on; eauto. *)
(*   unfold loc_out_of_bounds; intros. *)
(*   assert (Mem.perm m1 b i Max Nonempty). *)
(*   { apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem. *)
(*     exploit Mem.store_valid_access_3. eexact H3. intros [P Q]. eauto. } *)
(*   tauto. *)
(* Qed. *)

Lemma volatile_store_inject:
  forall ge1 ge2 f chunk m1 b ofs v t m2 m1' b' ofs' v',
  symbols_inject f ge1 ge2 ->
  volatile_store ge1 chunk m1 b ofs v t m2 ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  Val.inject f v v' ->
  Mem.inject f m1 m1' ->
  exists m2',
       volatile_store ge2 chunk m1' b' ofs' v' t m2'
    /\ Mem.inject f m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'.
Proof.
  intros until v'; intros SI VS AI VI MI.
  generalize SI; intros (P & Q & R & S).
  inv VS.
- (* volatile store *)
  inv AI. exploit Q; eauto. intros [A B]. subst delta.
  rewrite Ptrofs.add_zero. exists m1'; split.
  constructor; auto.
  { exploit Mem.perm_inject; eauto.
    replace (Ptrofs.unsigned ofs + 0) with (Ptrofs.unsigned ofs) by lia.
    eauto. }
  erewrite S; eauto.
  eapply eventval_match_inject; eauto. apply Val.load_result_inject. auto.
  intuition auto with mem.
- (* normal store *)
  inversion AI; subst.
  assert (Mem.storev chunk m1 (Vptr b ofs) v = Some m2). simpl; auto.
  exploit Mem.storev_mapped_inject; eauto. intros [m2' [A B]].
  exists m2'; intuition auto.
+ constructor; auto. erewrite S; eauto.
+ eapply Mem.store_unchanged_on; eauto.
  unfold loc_unmapped; intros. inv AI; congruence.
+ eapply Mem.store_unchanged_on; eauto.
  unfold loc_out_of_reach; intros. red; intros. simpl in A.
  assert (EQ: Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)) = Ptrofs.unsigned ofs + delta)
  by (eapply Mem.address_inject; eauto with mem).
  rewrite EQ in *.
  eelim H3; eauto.
  exploit Mem.store_valid_access_3. eexact H0. intros [X Y].
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  apply X. lia.
Qed.

Lemma volatile_store_receptive:
  forall ge chunk m b ofs v t1 m1 t2,
  volatile_store ge chunk m b ofs v t1 m1 -> match_traces ge t1 t2 -> t1 = t2.
Proof.
  intros. inv H; inv H0; auto.
Qed.

Lemma volatile_store_perm
  ge chunk m b ofs t v m'
  (VS: volatile_store ge chunk m b ofs v t m'):
  <<PERM: Mem.perm m b (Ptrofs.unsigned ofs) Cur Nonempty>>.
Proof.
  inv VS; ss. exploit Mem.store_valid_access_3; eauto. i. inv H1.
  r in H2. specialize (H2 (Ptrofs.unsigned ofs)).
  exploit H2; eauto; [destruct chunk; ss; lia|]. i.
  eapply Mem.perm_implies; eauto. eapply perm_any_N.
Qed.

Lemma volatile_store_ok:
  forall chunk,
  extcall_properties (volatile_store_sem chunk)
                     (mksignature (Tptr :: type_of_chunk chunk :: nil) Tvoid cc_default).
Proof.
  intros; constructor; intros.
  constructor; intros.
(* well typed *)
- unfold proj_sig_res; simpl. inv H; constructor.
(* symbols preserved *)
- inv H0. econstructor; eauto. eapply volatile_store_preserved; eauto.
(* valid block *)
- inv H. inv H1. auto. eauto with mem.
(* perms *)
- inv H. inv H2. auto. eauto with mem.
(* readonly *)
- inv H. eapply unchanged_on_readonly; eauto. eapply volatile_store_readonly; eauto.
(* bind *)
- inv H; ss. inv H1; ss. erewrite <- Mem.concrete_store; eauto.
(* nonempty *)
- inv H; ss. inv H1; ss. unfold nonempty_perm in *. des. split.
  { eapply Mem.perm_store_1; eauto. }
  i. eapply H1; eauto. eapply Mem.perm_store_2; eauto.
(* trace length *)
- inv H; inv H0; simpl; lia.  
(* mem extends*)
- inv H. inv H1. inv H6. inv H7.
  exploit Mem.to_ptr_extends; try eapply TOPTR; eauto. i. des.
  exploit volatile_store_extends; eauto. intros [m2' [A [B C]]].
  exists Vundef; exists m2'; intuition. econstructor; eauto.
(* mem inject *)
- inv H0. inv H2. inv H7. inv H8.
  exploit Mem.to_ptr_inject; try eapply H5; eauto. i. des. inv VINJ.
  exploit volatile_store_inject; eauto. intros [m2' [A [B [C D]]]].
  exists f; exists Vundef; exists m2'; intuition. econstructor; eauto. red; intros; congruence.
- inv H. inv H1. inv H6. inv H7.
  assert (PERM: Mem.perm m1 b (Ptrofs.unsigned ofs) Cur Nonempty).
  { inv H2; eauto. exploit Mem.store_valid_access_3; eauto. i.
    eapply Mem.valid_access_perm with (k := Cur) in H2. eapply Mem.perm_implies; eauto. eapply perm_any_N. }
  exploit to_ptr_concrete_exnteds; try eapply H4; eauto. intros TOPTR2.
  inv H2.
  2:{ exploit store_concrete_extends; eauto. i. des.
      exists E0. esplits; (try by econs); eauto.
      - econs; eauto. econs 2; eauto.
      - eapply Mem.store_unchanged_on; eauto.
        unfold loc_out_of_bounds; intros.
        assert (Mem.perm m1 b i Max Nonempty).
        { apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
          exploit Mem.store_valid_access_3. eexact H1. intros [P Q]. eauto. }
        tauto. }
  exploit (load_result_binded chunk); eauto. i.
  exploit eventval_match_binded; eauto. i. des.
  exists ([Event_vstore chunk id ofs ev2]). esplits; eauto; econs; ss; eauto.
  + econs; eauto. eapply concrete_extends_perm_implies; eauto.
  + eapply Ple_refl.
(* receptive *)
- assert (t1 = t2). inv H. eapply volatile_store_receptive; eauto.
  subst t2; exists vres1; exists m1; auto.
(* determ *)
- inv H; inv H0. clarify. inv H1; inv H7; try congruence.
  assert (id = id0) by (eapply Senv.find_symbol_injective; eauto). subst id0.
  assert (ev = ev0) by (eapply eventval_match_determ_2; eauto). subst ev0.
  split. constructor. auto.
  esplits; eauto. clarify.
(* concrete rev *)
- inv H. inv H1; eauto. erewrite Mem.concrete_store; eauto.
Qed.

(** ** Semantics of dynamic memory allocation (malloc) *)

Inductive extcall_malloc_sem (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_malloc_sem_intro: forall sz m m' b m'',
      Mem.alloc m (- size_chunk Mptr) (Ptrofs.unsigned sz) = (m', b) ->
      Mem.store Mptr m' b (- size_chunk Mptr) (Vptrofs sz) = Some m'' ->
      extcall_malloc_sem ge (Vptrofs sz :: nil) m E0 (Vptr b Ptrofs.zero) m''.

Lemma extcall_malloc_ok:
  extcall_properties extcall_malloc_sem
                     (mksignature (Tptr :: nil) Tptr cc_default).
Proof.
  assert (UNCHANGED:
    forall (P: block -> Z -> Prop) m lo hi v m' b m'',
    Mem.alloc m lo hi = (m', b) ->
    Mem.store Mptr m' b lo v = Some m'' ->
    Mem.unchanged_on P m m'').
  {
    intros.
    apply Mem.unchanged_on_implies with (fun b1 ofs1 => b1 <> b).
    apply Mem.unchanged_on_trans with m'.
    eapply Mem.alloc_unchanged_on; eauto.
    eapply Mem.store_unchanged_on; eauto.
    intros. eapply Mem.valid_not_valid_diff; eauto with mem.
  }
  constructor; intros.
  constructor; intros.
(* well typed *)
- inv H. simpl. unfold Tptr; destruct Archi.ptr64; auto.
(* symbols preserved *)
- inv H0; econstructor; eauto.
(* valid block *)
- inv H. eauto with mem.
(* perms *)
- inv H. exploit Mem.perm_alloc_inv. eauto. eapply Mem.perm_store_2; eauto.
  rewrite dec_eq_false. auto.
  apply Mem.valid_not_valid_diff with m1; eauto with mem.
(* readonly *)
- inv H. eapply unchanged_on_readonly; eauto. 
(* (* trace length *) *)
(* - inv H; simpl; lia. *)
(* bind *)
- inv H; ss. erewrite <- Mem.concrete_store; try eapply H2. erewrite <- Mem.concrete_alloc; eauto.
(* nonempty *)
- inv H; ss. unfold nonempty_perm in *. des.
  exploit Mem.perm_alloc_1; eauto. i. exploit Mem.perm_store_1; eauto. i.
  split; eauto. i. eapply H3. eapply Mem.perm_alloc_4; eauto.
  { eapply Mem.perm_store_2; eauto. }
  ii. subst. eapply Mem.fresh_block_alloc; eauto. eapply Mem.perm_valid_block; eauto.
(* trace length *)
- inv H; inv H0; simpl; lia.  
(* mem extends *)
- inv H. inv H1. inv H7.
  assert (SZ: v2 = Vptrofs sz).
  { unfold Vptrofs in *. destruct Archi.ptr64; inv H5; auto. }
  subst v2.
  exploit Mem.alloc_extends; eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m3' [A B]].
  exploit Mem.store_within_extends. eexact B. eauto. eauto.
  intros [m2' [C D]].
  exists (Vptr b Ptrofs.zero); exists m2'; intuition.
  econstructor; eauto.
  eapply UNCHANGED; eauto.
(* mem injects *)
- inv H0. inv H2. inv H8.
  assert (SZ: v' = Vptrofs sz).
  { unfold Vptrofs in *. destruct Archi.ptr64; inv H6; auto. }
  subst v'.
  exploit Mem.alloc_parallel_inject; eauto. apply Z.le_refl. apply Z.le_refl.
  intros [f' [m3' [b' [ALLOC [A [B [C D]]]]]]].
  exploit Mem.store_mapped_inject. eexact A. eauto. eauto.
  instantiate (1 := Vptrofs sz). unfold Vptrofs; destruct Archi.ptr64; constructor.
  rewrite Z.add_0_r. intros [m2' [E G]].
  exists f'; exists (Vptr b' Ptrofs.zero); exists m2'; intuition auto.
  econstructor; eauto.
  econstructor. eauto. auto.
  eapply UNCHANGED; eauto.
  eapply UNCHANGED; eauto.
  red; intros. destruct (eq_block b1 b).
  subst b1. rewrite C in H2. inv H2. eauto with mem.
  rewrite D in H2 by auto. congruence.
- inv H. inv H1. inv H7. inv H5. des_ifs.
  unfold Vptrofs in Heq. des_ifs.
  exploit alloc_concrete_extends; eauto. i. des.
  exploit store_concrete_extends; eauto.
  { econs. }
  i. des. esplits; eauto.
  { econs. }
  { econs; eauto. }
  eapply val_intptr_refl.
(* receptive *)
- assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
- inv H. simple inversion H0.
  assert (EQ2: sz0 = sz).
  { unfold Vptrofs in H4; destruct Archi.ptr64 eqn:SF.
    rewrite <- (Ptrofs.of_int64_to_int64 SF sz0), <- (Ptrofs.of_int64_to_int64 SF sz). congruence.
    rewrite <- (Ptrofs.of_int_to_int SF sz0), <- (Ptrofs.of_int_to_int SF sz). congruence.
  }
  subst.
  split. constructor. intuition congruence.
(* concrete rev *)
- inv H. erewrite Mem.concrete_alloc; cycle 1; eauto. erewrite Mem.concrete_store; eauto.
Qed.

(** ** Semantics of dynamic memory deallocation (free) *)

Inductive extcall_free_sem (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_free_sem_ptr: forall b lo sz m m' addr (TOPTR: Mem.to_ptr addr m = Some (Vptr b lo)),
      Mem.load Mptr m b (Ptrofs.unsigned lo - size_chunk Mptr) = Some (Vptrofs sz) ->
      Ptrofs.unsigned sz > 0 ->
      Mem.free m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) = Some m' ->
      extcall_free_sem ge (addr :: nil) m E0 Vundef m'
  | extcall_free_sem_null: forall m,
      extcall_free_sem ge (Vnullptr :: nil) m E0 Vundef m.

Lemma extcall_free_ok:
  extcall_properties extcall_free_sem
                     (mksignature (Tptr :: nil) Tvoid cc_default).
Proof.
  constructor; intros.
  constructor; intros.
(* well typed *)
- inv H; simpl; auto.
(* symbols preserved *)
- inv H0.
  { econs; eauto. }
  { econs 2; eauto. }
(* valid block *)
- inv H; eauto with mem.
(* perms *)
- inv H; eauto using Mem.perm_free_3.
(* readonly *)
- eapply unchanged_on_readonly; eauto. inv H.
+ eapply Mem.free_unchanged_on; eauto.
  intros. red; intros. elim H6.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.free_range_perm; eauto.
+ apply Mem.unchanged_on_refl.
- inv H; ss. erewrite <- Mem.concrete_free; try eapply H3. eauto.
(* nonempty *)
- inv H; ss.
  unfold nonempty_perm in *. des.
  hexploit Mem.free_range_perm; eauto. intros FPERM. r in FPERM.
  destruct (classic (Ptrofs.unsigned lo - size_chunk Mptr <= ofs < Ptrofs.unsigned lo + Ptrofs.unsigned sz)).
  { exploit FPERM; eauto. i.
    destruct (peq b0 b); subst.
    { eapply H4 in H5. clarify. }
    exploit Mem.perm_free_1; eauto. i. split; eauto. i.
    eapply Mem.perm_free_3 in H7; eauto. }
  eapply not_and_or in H. split.
  { exploit Mem.perm_free_1; eauto. right. des; lia. }
  i. eapply Mem.perm_free_3 in H5; eauto.
(* trace length *)
- inv H; simpl; lia.  
(* mem extends *)
- inv H.
+ inv H1. inv H8.
  exploit Mem.load_extends; eauto. intros [v' [A B]].
  assert (v' = Vptrofs sz).
  { unfold Vptrofs in *; destruct Archi.ptr64; inv B; auto. }
  subst v'.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [C D]].
  exists Vundef; exists m2'; intuition auto.
  econstructor; eauto.
  { eapply Mem.to_ptr_extends; try eapply TOPTR; eauto. }
  eapply Mem.free_unchanged_on; eauto.
  unfold loc_out_of_bounds; intros.
  assert (Mem.perm m1 b i Max Nonempty).
  { apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
    eapply Mem.free_range_perm. eexact H4. eauto. }
  tauto.
+ inv H1. inv H5. replace v2 with Vnullptr.
  exists Vundef; exists m1'; intuition auto.
  constructor.
  apply Mem.unchanged_on_refl.
  unfold Vnullptr in *; destruct Archi.ptr64; inv H3; auto.
(* mem inject *)
- inv H0.
+ inv H2. inv H9. rename v' into addr'.
  exploit Mem.to_ptr_inject; eauto. i. des. inv VINJ.
  exploit Mem.load_inject; eauto. intros [v' [A B]].
  assert (v' = Vptrofs sz).
  { unfold Vptrofs in *; destruct Archi.ptr64; inv B; auto. }
  subst v'.
  assert (P: Mem.range_perm m1 b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) Cur Freeable).
    eapply Mem.free_range_perm; eauto.
  exploit Mem.address_inject; eauto.
    apply Mem.perm_implies with Freeable; auto with mem.
    apply P. instantiate (1 := lo).
    generalize (size_chunk_pos Mptr); lia.
  intro EQ.
  exploit Mem.free_parallel_inject; eauto. intros (m2' & C & D).
  exists f, Vundef, m2'; split.
  eapply extcall_free_sem_ptr with (sz := sz) (m' := m2').
    eauto. eauto.
    rewrite EQ. rewrite <- A. f_equal. lia.
    auto. auto.
    rewrite ! EQ. rewrite <- C. f_equal; lia.
  split. auto.
  split. auto.
  split. eapply Mem.free_unchanged_on; eauto. unfold loc_unmapped. intros; congruence.
  split. eapply Mem.free_unchanged_on; eauto. unfold loc_out_of_reach.
    intros. red; intros. eelim H2; eauto.
    apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
    apply P. lia.
  split. auto.
  red; intros. congruence.
+ inv H2. inv H6. replace v' with Vnullptr.
  exists f, Vundef, m1'; intuition auto using Mem.unchanged_on_refl.
  constructor.
  red; intros; congruence.
  inv H4; auto.
- inv H; cycle 1.
  { inv H1. inv H5. inv H3. des_ifs. esplits; eauto; try by econs.
    - rewrite <- Heq. econs 2; eauto.
    - eapply Mem.unchanged_on_refl. }
  inv H1. inv H8. exploit to_ptr_concrete_exnteds; eauto.
  { eapply Mem.free_range_perm in H4. specialize (H4 (Ptrofs.unsigned lo)). exploit H4.
    { unfold Mptr. des_ifs. ss. lia. }
    i. eapply Mem.perm_cur. eapply Mem.perm_implies; eauto. eapply perm_any_N. }
  i. exploit load_concrete_extends; eauto. i. des.
  exploit free_concrete_extends; eauto. i. des.
  esplits; eauto; try by econs.
  + econs; eauto. inv BIND. des_ifs.
  + eapply Mem.free_unchanged_on; eauto.
    unfold loc_out_of_bounds; intros.
    assert (Mem.perm m1 b i Max Nonempty).
    { apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
      eapply Mem.free_range_perm. eexact H4. eauto. }
    tauto.
(* receptive *)
- assert (t1 = t2) by (inv H; inv H0; auto). subst t2.
  exists vres1; exists m1; auto.
(* determ *)
- inv H; inv H0; try (unfold Vnullptr in *; destruct Archi.ptr64; discriminate).
+ rewrite TOPTR0 in TOPTR. inv TOPTR.
  assert (EQ1: Vptrofs sz0 = Vptrofs sz) by congruence.
  assert (EQ2: sz0 = sz).
  { unfold Vptrofs in EQ1; destruct Archi.ptr64 eqn:SF.
    rewrite <- (Ptrofs.of_int64_to_int64 SF sz0), <- (Ptrofs.of_int64_to_int64 SF sz). congruence.
    rewrite <- (Ptrofs.of_int_to_int SF sz0), <- (Ptrofs.of_int_to_int SF sz). congruence.
  }
  subst sz0.
  split. constructor. intuition congruence.
+ split. constructor. intuition auto.
(* concrete rev *)
- inv H; eauto. erewrite Mem.concrete_free; cycle 1; eauto.
  Unshelve. econs.
Qed.

(** ** Semantics of [memcpy] operations. *)

Inductive extcall_memcpy_sem (sz al: Z) (ge: Senv.t):
                        list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_memcpy_sem_intro: forall bdst odst bsrc osrc m bytes m' addr addr' (SZ: sz > 0)
                                (TOPTR1: Mem.to_ptr addr m = Some (Vptr bdst odst))
                                (TOPTR2: Mem.to_ptr addr' m = Some (Vptr bsrc osrc)),
      al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz >= 0 -> (al | sz) ->
      (sz > 0 -> (al | Ptrofs.unsigned osrc)) ->
      (sz > 0 -> (al | Ptrofs.unsigned odst)) ->
      bsrc <> bdst \/ Ptrofs.unsigned osrc = Ptrofs.unsigned odst
                   \/ Ptrofs.unsigned osrc + sz <= Ptrofs.unsigned odst
                   \/ Ptrofs.unsigned odst + sz <= Ptrofs.unsigned osrc ->
      Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) sz = Some bytes ->
      Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes = Some m' ->
      extcall_memcpy_sem sz al ge (addr :: addr' :: nil) m E0 Vundef m'
  | extcall_memcpy_sem_zero: forall m addr addr' (SZ: sz = 0),
      extcall_memcpy_sem sz al ge (addr :: addr' :: nil) m E0 Vundef m  
.

Lemma extcall_memcpy_ok:
  forall sz al,
  extcall_properties (extcall_memcpy_sem sz al)
                     (mksignature (Tptr :: Tptr :: nil) Tvoid cc_default).
Proof.
  intros. constructor.
  intros. constructor.
- (* return type *)
  intros. inv H; exact I.
- (* change of globalenv *)
  intros. inv H0. econstructor; eauto.
  econs 2; eauto.
- (* valid blocks *)
  intros. inv H; eauto with mem.
- (* perms *)
  intros. inv H. eapply Mem.perm_storebytes_2; eauto.
  eauto.
- (* readonly *)
  intros. inv H. eapply unchanged_on_readonly; eauto. 
  eapply Mem.storebytes_unchanged_on; eauto.
  intros; red; intros. elim H11.
  apply Mem.perm_cur_max. eapply Mem.storebytes_range_perm; eauto.
  eauto.
- i. inv H. erewrite <- Mem.concrete_storebytes; eauto. ss.
(* nonempty *)
- ii. inv H; ss. unfold nonempty_perm in *. des_safe.
  exploit Mem.perm_storebytes_1; eauto. i. split; auto. i.
  eapply Mem.perm_storebytes_2 in H10; eauto.
- (* trace length *)
  intros; inv H; simpl; lia.  
- (* extensions *)
  intros. inv H.
  inv H1. inv H13. inv H14. (* inv H14. inv H10. inv H11. *)
  exploit Mem.loadbytes_length; eauto. intros LEN.
  exploit Mem.loadbytes_extends; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_within_extends; eauto. intros [m2' [C D]].
  exists Vundef; exists m2'.
  exploit Mem.to_ptr_extends; try eapply TOPTR1; eauto. i. des_safe.
  exploit Mem.to_ptr_extends; try eapply TOPTR2; eauto. i. des_safe.
  assert (v2 = addr /\ v0 = addr').
  { destruct addr; destruct addr'; ss; inv H11; inv H10; eauto. }
  des_safe; subst.
  split. econstructor; eauto.
  split. constructor.
  split. auto.
  eapply Mem.storebytes_unchanged_on; eauto. unfold loc_out_of_bounds; intros.
  assert (Mem.perm m1 bdst i Max Nonempty).
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  eapply Mem.storebytes_range_perm; eauto.
  erewrite list_forall2_length; eauto.
  tauto.
  { inv H1. inv H5. inv H6. esplits; eauto; [econs 2; eauto| eapply Mem.unchanged_on_refl]. }
- (* injections *)
  intros. inv H0. inv H2. inv H14. inv H15. (* inv H11. inv H12. *)
  exploit Mem.to_ptr_inject; try eapply TOPTR1; eauto. intros (v1' & TOPTR1' & INJ1). des_safe.
  exploit Mem.to_ptr_inject; try eapply TOPTR2; eauto. intros (v0' & TOPTR2' & INJ0). des_safe.
  inv INJ0. inv INJ1. 
+ (* general case sz > 0 *)
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (RPSRC: Mem.range_perm m1 bsrc (Ptrofs.unsigned osrc) (Ptrofs.unsigned osrc + sz) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m1 bdst (Ptrofs.unsigned odst) (Ptrofs.unsigned odst + sz) Cur Nonempty).
    replace sz with (Z.of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply Z2Nat.id. lia.
  assert (PSRC: Mem.perm m1 bsrc (Ptrofs.unsigned osrc) Cur Nonempty).
    apply RPSRC. lia.
  assert (PDST: Mem.perm m1 bdst (Ptrofs.unsigned odst) Cur Nonempty).
    apply RPDST. lia.
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [m2' [C D]].
  exists f; exists Vundef; exists m2'.
  split. econstructor; try eapply TOPTR1'; try eapply TOPTR0'; try rewrite EQ1; try rewrite EQ2; eauto.
  intros; eapply Mem.aligned_area_inject with (m := m1); eauto.
  intros; eapply Mem.aligned_area_inject with (m := m1); eauto.
  eapply Mem.disjoint_or_equal_inject with (m := m1); eauto.
  apply Mem.range_perm_max with Cur; auto.
  apply Mem.range_perm_max with Cur; auto. (* lia. *)
  split. constructor.
  split. auto.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_unmapped; intros.
  congruence.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_out_of_reach; intros. red; intros.
  eelim H2; eauto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  eapply Mem.storebytes_range_perm; eauto.
  erewrite list_forall2_length; eauto.
  lia.
  split. apply inject_incr_refl.
  red; intros; congruence.
+ (* special case sz = 0 *)
  inv H2. inv H6. inv H7.
  esplits; eauto.
  econs 2; eauto.
  eapply Mem.unchanged_on_refl.
  eapply Mem.unchanged_on_refl.
  red; intros; congruence.
- i. inv H; cycle 1.
  { esplits; eauto; try by econs.
    - inv H1. inv H5. inv H6. econs 2. eauto.
    - eapply Mem.unchanged_on_refl. }
  inv H1. inv H13. inv H14.
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (RPSRC: Mem.range_perm m1 bsrc (Ptrofs.unsigned osrc) (Ptrofs.unsigned osrc + sz) Cur Nonempty).
  { eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem. }
  assert (RPDST: Mem.range_perm m1 bdst (Ptrofs.unsigned odst) (Ptrofs.unsigned odst + sz) Cur Nonempty).
  { replace sz with (Z.of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply Z2Nat.id. lia. }
  assert (PSRC: Mem.perm m1 bsrc (Ptrofs.unsigned osrc) Cur Nonempty).
  { apply RPSRC. lia. }
  assert (PDST: Mem.perm m1 bdst (Ptrofs.unsigned odst) Cur Nonempty).
  { apply RPDST. lia. }
  exploit to_ptr_concrete_exnteds; try eapply TOPTR1; eauto. i.
  exploit to_ptr_concrete_exnteds; try eapply TOPTR2; eauto. i.
  exploit loadbytes_concrete_extends; eauto. i. des_safe.
  exploit storebytes_within_concrete_extends; eauto. i. des_safe.
  exists E0, Vundef, m2'. esplits; eauto; try by econs.
  + econs; eauto.
  + eapply Mem.storebytes_unchanged_on; eauto. unfold loc_out_of_bounds; intros.
    assert (Mem.perm m1 bdst i Max Nonempty).
    apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
    eapply Mem.storebytes_range_perm; eauto.
    erewrite list_forall2_length; eauto.
    tauto.
- (* receptive *)
  intros.
  assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
- (* determ *)
  intros; inv H; inv H0. split. constructor. intros; split; congruence.
  lia. lia. esplits; eauto.
(* concrete rev *)
- i. inv H; eauto. erewrite Mem.concrete_storebytes; cycle 1; eauto.
Qed.

(** ** Semantics of annotations. *)

Inductive extcall_annot_sem (text: string) (targs: list typ) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_annot_sem_intro: forall vargs m args,
      eventval_list_match ge args targs vargs ->
      extcall_annot_sem text targs ge vargs m (Event_annot text args :: E0) Vundef m.

Lemma extcall_annot_ok:
  forall text targs,
  extcall_properties (extcall_annot_sem text targs)
                     (mksignature targs Tvoid cc_default).
Proof.
  intros; constructor; intros.
  constructor; intros.
(* well typed *)
- inv H. simpl. auto.
(* symbols *)
- destruct H as (A & B & C). inv H0. econstructor; eauto.
  eapply eventval_list_match_preserved; eauto.
(* valid blocks *)
- inv H; auto.
(* perms *)
- inv H; auto.
(* readonly *)
- inv H; auto.
- inv H; ss.
- inv H; ss.
(* trace length *)
- inv H; simpl; lia.
(* mem extends *)
- inv H.
  exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_lessdef; eauto.
(* mem injects *)
- inv H0.
  exists f; exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_inject; eauto.
  red; intros; congruence.
- inv H. exploit eventval_list_match_binded; eauto. i. des.
  exists (Event_annot text evl2 :: E0), Vundef, m1'. esplits; eauto; try by econs.
  + econs; eauto; econs; eauto.
  + eapply Mem.unchanged_on_refl.
(* receptive *)
- assert (t1 = t2). inv H; inv H0; auto.
  exists vres1; exists m1; congruence.
(* determ *)
- inv H; inv H0.
  assert (args = args0). eapply eventval_list_match_determ_2; eauto. subst args0.
  split. constructor. auto.
(* concrete rev *)
- inv H; eauto.
Qed.

Inductive extcall_annot_val_sem (text: string) (targ: typ) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_annot_val_sem_intro: forall varg m arg,
      eventval_match ge arg targ varg ->
      extcall_annot_val_sem text targ ge (varg :: nil) m (Event_annot text (arg :: nil) :: E0) varg m.

Lemma extcall_annot_val_ok:
  forall text targ,
  extcall_properties (extcall_annot_val_sem text targ)
                     (mksignature (targ :: nil) targ cc_default).
Proof.
  intros; constructor; intros.
  constructor; intros.
(* well typed *)
- inv H. eapply eventval_match_type; eauto.
(* symbols *)
- destruct H as (A & B & C). inv H0. econstructor; eauto.
  eapply eventval_match_preserved; eauto.
(* valid blocks *)
- inv H; auto.
(* perms *)
- inv H; auto.
(* readonly *)
- inv H; auto.
- inv H. ss.
- inv H. ss.
(* trace length *)
- inv H; simpl; lia.
(* mem extends *)
- inv H. inv H1. inv H6.
  exists v2; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_match_lessdef; eauto.
(* mem inject *)
- inv H0. inv H2. inv H7.
  exists f; exists v'; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_match_inject; eauto.
  red; intros; congruence.
- inv H. inv H1. inv H6. exploit eventval_match_binded; eauto. i. des.
  exists (Event_annot text [ev2] :: E0). esplits; eauto.
  { econs; econs; eauto. }
  + econs. eauto.
  + eapply Mem.unchanged_on_refl.
(* receptive *)
- assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
- inv H; inv H0.
  assert (arg = arg0). eapply eventval_match_determ_2; eauto. subst arg0.
  split. constructor. auto.
(* concrete rev *)
- inv H; eauto.
Qed.

Inductive extcall_debug_sem (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_debug_sem_intro: forall vargs m,
      extcall_debug_sem ge vargs m E0 Vundef m.

Lemma extcall_debug_ok:
  forall targs,
  extcall_properties extcall_debug_sem
                     (mksignature targs Tvoid cc_default).
Proof.
  intros; constructor; intros.
  constructor; intros.
(* well typed *)
- inv H. simpl. auto.
(* symbols *)
- inv H0. econstructor; eauto.
(* valid blocks *)
- inv H; auto.
(* perms *)
- inv H; auto.
(* readonly *)
- inv H; auto.
- inv H; ss.
- inv H; ss.
(* trace length *)
- inv H; simpl; lia.
(* mem extends *)
- inv H.
  exists Vundef; exists m1'; intuition.
  econstructor; eauto.
(* mem injects *)
- inv H0.
  exists f; exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  red; intros; congruence.
- inv H. esplits; eauto. econs. econs. econs.
  eapply Mem.unchanged_on_refl.
(* receptive *)
- inv H; inv H0. exists Vundef, m1; constructor.
(* determ *)
- inv H; inv H0.
  split. constructor. auto.
(* concrete rev *)
- inv H; eauto.
Qed.

(** ** Semantics of known built-in functions. *)

(** Some built-in functions and runtime support functions have known semantics
  as defined in the [Builtin] modules.
  These built-in functions have no observable effects and do not access memory. *)

Inductive known_builtin_sem (bf: builtin_function) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | known_builtin_sem_intro: forall vargs vres m,
      builtin_function_sem bf vargs = Some vres ->
      known_builtin_sem bf ge vargs m E0 vres m.

Lemma known_builtin_ok: forall bf,
  extcall_properties (known_builtin_sem bf) (builtin_function_sig bf).
Proof.
  intros. set (bsem := builtin_function_sem bf). constructor; intros.
  constructor; intros.
(* well typed *)
- inv H.
  specialize (bs_well_typed  _ bsem vargs).
  unfold val_opt_has_rettype, bsem; rewrite H0.
  auto.
(* symbols *)
- inv H0. econstructor; eauto.
(* valid blocks *)
- inv H; auto.
(* perms *)
- inv H; auto.
(* readonly *)
- inv H; auto.
- inv H; ss.
- inv H; ss.
(* trace length *)
- inv H; simpl; lia.
(* mem extends *)
- inv H. fold bsem in H2. apply val_inject_list_lessdef in H1.
  specialize (bs_inject _ bsem _ _ _ H1).
  unfold val_opt_inject; rewrite H2; intros.
  destruct (bsem vargs') as [vres'|] eqn:?; try contradiction.
  exists vres', m1'; intuition auto using Mem.extends_refl, Mem.unchanged_on_refl.
  constructor; auto.
  apply val_inject_lessdef; auto.
(* mem injects *)
- inv H0. fold bsem in H3.
  specialize (bs_inject _ bsem _ _ _ H2).
  unfold val_opt_inject; rewrite H3; intros.
  destruct (bsem vargs') as [vres'|] eqn:?; try contradiction.
  exists f, vres', m1'; intuition auto using Mem.extends_refl, Mem.unchanged_on_refl.
  constructor; auto.
  red; intros; congruence.
- inv H. fold bsem in H2.
  specialize (bs_binded _ bsem _ _ _ H1).
  unfold val_opt_binded. rewrite H2. i. des_ifs.
  esplits; eauto.
  { econs. }
  { econs; eauto. }
  eapply Mem.unchanged_on_refl.
(* receptive *)
- inv H; inv H0. exists vres1, m1; constructor; auto. 
(* determ *)
- inv H; inv H0.
  split. constructor. intuition congruence.
(* concrete rev *)
- inv H; eauto.
Qed.

Inductive extcall_capture_sem (ge: Senv.t):
  list val -> mem -> trace -> val -> mem -> Prop :=
| extcall_capture_sem_intro
    b m m' addr ofs v
    (CAPTURE: Mem.capture m b addr m')
    (RET: v = if Archi.ptr64
              then Vlong (Int64.repr (addr + (Ptrofs.unsigned ofs)))
              else Vint (Int.repr (addr + (Ptrofs.unsigned ofs)))) :
    extcall_capture_sem ge (Vptr b ofs :: nil) m E0 v m'
| extcall_capture_sem_fail
    b m ofs
    (OOM: Mem.capture_oom m b) :
    extcall_capture_sem ge (Vptr b ofs :: nil) m [Event_pterm] Vundef m
| extcall_capture_int
    (PTRSZ: Archi.ptr64 = false)
    m n :
    extcall_capture_sem ge (Vint n :: nil) m E0 (Vint n) m
| extcall_capture_long
    (PTRSZ: Archi.ptr64 = true)
    m n :
    extcall_capture_sem ge (Vlong n :: nil) m E0 (Vlong n) m.

Lemma capture_extends_backward
    m1 b addr m1' m2'
    (CAPTGT: Mem.capture m1' b addr m2')
    (MEXT: Mem.extends m1 m1') :
  (exists m2, <<CAPSRC: Mem.capture m1 b addr m2>>
    /\ <<MEXT: Mem.extends m2 m2'>>
    /\ <<PRIV: Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'>>).
Proof.
  exploit Mem.capture_extends_backward; eauto. i. des. esplits; eauto.
  inversion CAPTGT. econs; eauto.
  - rewrite NEXTBLOCK. eapply Ple_refl.
  - i. unfold Mem.perm. rewrite ACCESS. auto.
  - i. rewrite CONTENTS. auto.
  - i. destruct (peq b0 b).
    { subst. exploit PREVADDR; eauto. i. des. rewrite <- H2. clarify. }
    { exploit Mem.concrete_other. eapply CAPTGT. eauto. i. rewrite <- H1. auto. }
Qed.

Lemma capture_extends_backward_progress
    m1 m2 b addr m1'
    (CAPSRC: Mem.capture m1 b addr m2)
    (MEXT: Mem.extends m1 m1') :
  (exists m2' addr, <<CAPTGT: Mem.capture m1' b addr m2'>>) \/ <<OOM: Mem.capture_oom m1' b>>.
Proof. exploit Mem.capture_extends_backward_progress; eauto. Qed.

Lemma capture_injects_backward
    m1' b' m2' f m1 b ofs ofs' delta addr
    (FB: f b = Some (b', delta))
    (CAPTGT: Mem.capture m1' b' (addr - delta) m2')
    (MINJ: Mem.inject f m1 m1')
    (VINJ: Val.inject f (Vptr b ofs) (Vptr b' ofs')) :
  (exists f' m2,
    <<CAPSRC: Mem.capture m1 b addr m2>>
    /\ <<MINJ: Mem.inject f' m2 m2'>>
    /\ <<MEMPRIVSRC: Mem.unchanged_on (loc_unmapped f) m1 m2>>
    /\ <<MEMPRIVTGT: Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'>>
    /\ <<INJINCR: inject_incr f f'>>
    /\ <<INJSEP: inject_separated f f' m1 m1'>>).
Proof.
  exploit Mem.capture_inject_backward; try eapply FB; eauto. i. des.
  esplits; eauto.
  - inversion CAPSRC. econs.
    + rewrite NEXTBLOCK. eapply Ple_refl.
    + i. inv H. unfold Mem.perm. rewrite ACCESS. auto.
    + i. rewrite CONTENTS. auto.
    + i. destruct (peq b0 b).
      * subst. exploit PREVADDR; eauto. i. des. rewrite <- H2. clarify.
      * exploit Mem.concrete_other. eapply CAPSRC. eauto. i. rewrite <- H1. auto.
  - inversion CAPTGT. econs.
    + rewrite NEXTBLOCK. eapply Ple_refl.
    + i. unfold Mem.perm. rewrite ACCESS. auto.
    + i. rewrite CONTENTS. auto.
    + i. destruct (peq b0 b').
      * subst. exploit PREVADDR; eauto. i. des. rewrite <- H2. clarify.
      * exploit Mem.concrete_other. eapply CAPTGT. eauto. i. rewrite <- H1. auto.
  - split; clarify.
Qed.

Lemma capture_injects_backward_progress
    m1 b addr m1' f m2 b' ofs ofs' delta
    (FB: f b = Some (b', delta))
    (CAPSRC: Mem.capture m1 b addr m2)
    (MINJ: Mem.inject f m1 m1')
    (VINJ: Val.inject f (Vptr b ofs) (Vptr b' ofs')) :
  (exists m2' addr', <<CAPTGT: Mem.capture m1' b' addr' m2'>>) \/ <<OOM: Mem.capture_oom m1' b'>>.
Proof. exploit Mem.capture_injects_backward_progress; eauto. Qed.

Lemma capture_concrete_extends_backward
    m1 b addr m1' m2'
    (CAPTGT: Mem.capture m1' b addr m2')
    (CONC: concrete_extends m1 m1') :
  (exists m2,
    <<CAPSRC: Mem.capture m1 b addr m2>>
    /\ <<CONC: concrete_extends m2 m2'>>
    /\ <<PRIV: Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'>>).
Proof.
  exploit capture_concrete_extends; eauto. i. des. esplits; eauto.
  inversion CAPTGT. econs; eauto.
  - rewrite NEXTBLOCK. eapply Ple_refl.
  - i. unfold Mem.perm. rewrite ACCESS. auto.
  - i. rewrite CONTENTS. auto.
  - i. destruct (peq b0 b).
    { subst. exploit PREVADDR; eauto. i. des. rewrite <- H2. clarify. }
    { exploit Mem.concrete_other. eapply CAPTGT. eauto. i. rewrite <- H1. auto. }
Qed.

Lemma extcall_capture_ok:
  extcall_properties_backward extcall_capture_sem
                              (mksignature (Tptr :: nil) (if Archi.ptr64 then Tlong else Tint) cc_default).
Proof.
  econs; i. econs; i.
(* well typed *)
- inv H; unfold proj_sig_res; ss.
(* symbols *)
- inv H0. econs; eauto. econs 2; eauto. econs; eauto. econs; eauto.
(* valid blocks *)
- inv H; eauto. inv CAPTURE. unfold Mem.valid_block in *. rewrite <- NEXTBLOCK. eauto.
(* max perms *)
- inv H; try inv CAPTURE; unfold Mem.perm in *; try rewrite ACCESS; auto.
(* readonly *)
- inv H; eauto.
  inversion CAPTURE.
  erewrite <- Mem.loadbytes_capture_unchanged; eauto.
(* (* trace length *) *)
(* - inv H; simpl; lia. *)
- inv H; ss. inv CAPTURE.
  destruct (peq b b0); subst.
  { exploit PREVADDR; eauto. i. des. rewrite <- H1. eauto. }
  destruct (Maps.PTree.get b0 (Mem.mem_concrete m1)) eqn:CAP.
  + exploit PREVADDR; eauto. i. des; clarify. rewrite <- H1; eauto.
  + exploit CAPTURED; eauto. i. rewrite H. rewrite Maps.PTree.gso; eauto.
- inv H; ss. unfold nonempty_perm in *. des.
  rewrite Genv.capture_same_perm in H0; eauto. split; eauto. i.
  rewrite <- Genv.capture_same_perm in H; eauto.
(* mem extends *)
- inversion CALLTGT; subst; cycle 1.
  { inv ARGS. inv H2; inv H3; cycle 1.
    - right. left. ii. inv H.
    - destruct (classic (Mem.valid_block m1 b)); cycle 1.
      { right. left. ii. inv H0. inv CAPTURE; clarify.
        inv OOM0; clarify. }
      destruct OOM.
      destruct (classic (exists addr' m'', Mem.capture m1 b addr' m'')).
      + des. right. right. esplits; ss.
        * unfold trace_intact. ss. ii. eapply H3. eauto.
        * traceEq. econs; eauto.
      + right. right. esplits; eauto.
        * unfold trace_intact. ss. ii. eapply H3. eauto.
        * traceEq. econs 2; eauto. split; eauto. }
  { inv ARGS. inv H3. inv H2.
    - left. exists (Vint n). exists m1. esplits; eauto.
      { econs; eauto. }
      { eapply Mem.unchanged_on_refl. }
    - right. left. ii. inv H. }
  { inv ARGS. inv H3. inv H2.
    - left. exists (Vlong n). exists m1. esplits; eauto.
      { econs; eauto. }
      { eapply Mem.unchanged_on_refl. }
    - right. left. ii. inv H. }
  inv ARGS; inv H2; inv H3; cycle 1.
  { right. left. ii. inv H. }
  exploit capture_extends_backward; eauto. i. des.
  left. exists (if Archi.ptr64 then Vlong (Int64.repr (addr + Ptrofs.unsigned ofs))
           else Vint (Int.repr (addr + Ptrofs.unsigned ofs))).
  esplits; eauto. econs; eauto.
(* mem extends progress *)
- inversion CALLSRC; subst; inv ARGS; inv H1; inv H3; cycle 1.
  { exists [Event_pterm], Vundef. eexists.
    red. econs 2; eauto.
    inv OOM. split.
    erewrite <- Mem.valid_block_extends; eauto.
    ii. exploit capture_extends_backward; eauto. i. des.
    eapply H0. eauto. }
  { esplits; eauto. econs; eauto. }
  { esplits; eauto. econs; eauto. }
  exploit capture_extends_backward_progress; eauto. i. des.
  + esplits. econs; eauto.
  + exists [Event_pterm], Vundef. eexists.
    red. econs 2; eauto.
(* mem injects *)
- inversion CALLTGT; subst; cycle 1.
  { inv ARGS. inv H2; inv H3; cycle 1.
    - right. left. ii. inv H.
    - destruct (classic (Mem.valid_block m1 b1)); cycle 1.
      { right. left. ii. inv H0. inv CAPTURE; clarify.
        inv OOM0; clarify. }
      destruct OOM.
      destruct (classic (exists addr' m'', Mem.capture m1 b1 addr' m'')).
      + des. right. right. esplits; ss.
        * unfold trace_intact. ss. ii. eapply H3. eauto.
        * traceEq. econs; eauto.
      + right. right. esplits; eauto.
        * unfold trace_intact. ss. ii. eapply H3. eauto.
        * traceEq. econs 2; eauto. split; eauto. }
  { inv ARGS. inv H3. inv H2.
    - left. exists f. exists (Vint n). exists m1. esplits; eauto.
      econs; eauto. eapply Mem.unchanged_on_refl. eapply Mem.unchanged_on_refl.
      rr. ii. clarify.
    - right. left. ii. inv H. }
  { inv ARGS. inv H3. inv H2.
    - left. exists f. exists (Vlong n). exists m1. esplits; eauto.
      econs; eauto. eapply Mem.unchanged_on_refl. eapply Mem.unchanged_on_refl.
      rr. ii. clarify.
    - right. left. ii. inv H. }
  inv ARGS. inv H3. inv H2; cycle 1.
  { right. left. ii. inv H. }
  des_ifs.
  exploit capture_injects_backward; eauto.
  instantiate (2:= (addr + delta)).
  assert ((addr + delta - delta) = addr). lia.
  rewrite H. eauto. i. des.
  left. exists f', (if Archi.ptr64
               then Vlong (Int64.repr (addr + delta + Ptrofs.unsigned ofs1))
               else Vint (Int.repr (addr + delta + Ptrofs.unsigned ofs1))).
  esplits; eauto. des_ifs. econs; eauto.
  des_ifs.
  assert ((Int64.repr (addr + delta + Ptrofs.unsigned ofs1)) = (Int64.repr (addr + Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta))))).
  { apply Int64.eqm_samerepr. rewrite Zplus_assoc_reverse. eapply Int64.eqm_add. eapply Int64.eqm_refl.
    rewrite Ptrofs.eqm64; eauto. rewrite Ptrofs.add_unsigned. eapply Ptrofs.eqm_unsigned_repr_r.
    assert (delta + Ptrofs.unsigned ofs1 = Ptrofs.unsigned ofs1 + delta) by lia. rewrite H.
    eapply Ptrofs.eqm_add. eapply Ptrofs.eqm_refl. eapply Ptrofs.eqm_unsigned_repr. }
  rewrite H. econs.
(* mem injects progress *)
- inversion CALLSRC; subst; inv ARGS; inv H1; inv H3; cycle 1.
  { exists [Event_pterm], Vundef. eexists.
    red. econs 2; eauto.
    inv OOM. split.
    { eapply Mem.valid_block_inject_2; eauto. }
    ii.
    assert ((addr + delta - delta) = addr). lia.
    exploit capture_injects_backward; eauto. erewrite H3. eauto. i. des.
    eapply H0; eauto. }
  { esplits. econs; eauto. }
  { esplits. econs; eauto. }
  inv SYMB. des.
  exploit capture_injects_backward_progress; eauto. i. des.
  + esplits. econs; eauto.
  + exists [Event_pterm], Vundef. eexists.
    red. econs 2; eauto.
(* self-inj *)
- inv CALLSRC; cycle 1.
  { inv OOM. esplits; eauto.
    - eapply Mem.unchanged_on_refl.
    - eapply Mem.unchanged_on_refl.
    - ii; clarify. }
  { exists f. esplits; eauto. eapply Mem.unchanged_on_refl.
    eapply Mem.unchanged_on_refl. ii. clarify. }
  { exists f. esplits; eauto. eapply Mem.unchanged_on_refl.
    eapply Mem.unchanged_on_refl. ii. clarify. }
  inv ARGS. inv H2. exploit SELF; eauto. i. des; subst.
  inv MEM. inversion CAPTURE.
  exists f. esplits; eauto.
  + des_ifs.
  + econs.
    * inv mi_inj. econs.
      { unfold Mem.perm, Mem.perm_order' in *. rewrite <- ACCESS. eauto. }
      { unfold Mem.range_perm, Mem.perm, Mem.perm_order' in *. rewrite <- ACCESS. eauto. }
      { i. exploit SELF; eauto. i. des; subst.
        rewrite Z.add_0_r.
        exploit mi_memval; eauto.
        unfold Mem.perm, Mem.perm_order' in *. rewrite ACCESS. eauto. i.
        rewrite Z.add_0_r in H2. rewrite <- CONTENTS. eauto. }
    * unfold Mem.valid_block in *. rewrite <- NEXTBLOCK in *. eauto.
    * unfold Mem.valid_block in *. rewrite <- NEXTBLOCK in *. eauto.
    * unfold Mem.meminj_no_overlap in *.
      unfold Mem.perm, Mem.perm_order' in *. rewrite <- ACCESS. eauto.
    * unfold Mem.perm, Mem.perm_order' in *. rewrite <- ACCESS. eauto.
    * unfold Mem.perm, Mem.perm_order' in *. rewrite <- ACCESS. eauto.
    * i. exploit SELF; eauto. i. des; subst. rewrite Z.sub_0_r. eauto.
    * i.
      destruct (peq b b0).
      { subst. clarify. }
      destruct (Maps.PTree.get b (Mem.mem_concrete m1)).
      { exploit PREVADDR; eauto. i. des; subst.
        rewrite <- H1. eauto. }
      rewrite CAPTURED; eauto. rewrite Maps.PTree.gso; eauto.
  + eapply Mem.capture_unchanged_on; eauto.
  + eapply Mem.capture_unchanged_on; eauto.
  + ii. clarify.
- destruct (classic (exists t vres m2, extcall_capture_sem ge vargs m1 t vres m2)); cycle 1.
  { right. left. ii. eapply H2; eauto. }
  des. rename H2 into SAFE.
  inv H; ss.
  + exploit capture_concrete_extends_backward; eauto. i. des.
    inv H1. inv H5. inv H4; cycle 1.
    { inv SAFE. }
    left. exists E0. esplits; eauto; try by econs.
    econs; eauto.
  + right. right. split.
    { ii. eapply H. ss. auto. }
    esplits; eauto. traceEq. eapply tr_rel_refl. eapply ev_rel_refl.
  + inv H1. inv H5. inv H4; ss.
    3:{ inv SAFE. }
    * left. exists E0. esplits; eauto; try by econs.
      eapply Mem.unchanged_on_refl.
    * des_ifs_safe. left.
      unfold Mem.ptr2int in Heq. des_ifs.
      assert (Mem.capture m2' b z0 m2').
      { econs; eauto.
        - eapply NNPP. ii. eapply Mem.nextblocks_logical in H. clarify.
        - i. clarify.
        - i. clarify. }
      exploit capture_concrete_extends; eauto. i. des.
      exists E0. esplits; eauto; try by econs.
      { econs; eauto. }
      eapply Mem.unchanged_on_refl.
(* CE progress *)
- inv CALLSRC; ss.
  + inv ARGS. inv H1; inv H3; ss.
    * exploit capture_concrete_extends_backward_progress; eauto. i. des.
      { esplits. econs; eauto. }
      esplits. econs 2. eauto.
    * esplits; eauto. econs. eauto.
  + inv ARGS. inv H1; inv H3; ss.
    { exists [Event_pterm], Vundef. eexists.
      red. econs 2; eauto.
      inv OOM. split.
      { unfold Mem.valid_block in *. erewrite <- same_nextblock; eauto. }
      ii. exploit capture_concrete_extends; eauto. i. des.
      eapply H0. eauto. }
    esplits. econs; eauto.
  + inv ARGS. inv H1. inv H3. esplits; eauto. econs. eauto.
Unshelve. all: eauto.
Qed.

(** ** Semantics of external functions. *)

(** For functions defined outside the program ([EF_external]),
  we do not define their semantics, but only assume that it satisfies
  [extcall_properties].
  We do the same for built-in functions and runtime support functions that
  are not described in [Builtins].
*)

Parameter external_functions_sem: String.string -> signature -> extcall_sem.

Axiom external_functions_properties:
  forall id sg, extcall_properties_backward (external_functions_sem id sg) sg.

(** We treat inline assembly similarly. *)

Parameter inline_assembly_sem: String.string -> signature -> extcall_sem.

Axiom inline_assembly_properties:
  forall id sg, extcall_properties_backward (inline_assembly_sem id sg) sg.

(** ** Combined semantics of external calls *)

Definition builtin_or_external_sem name sg :=
  match lookup_builtin_function name sg with
  | Some bf => known_builtin_sem bf
  | None => external_functions_sem name sg
  end.

(* Lemma builtin_or_external_sem_ok: forall name sg, *)
(*   extcall_properties (builtin_or_external_sem name sg) sg. *)
(* Proof. *)
(*   unfold builtin_or_external_sem; intros.  *)
(*   destruct (lookup_builtin_function name sg) as [bf|] eqn:L. *)
(* - exploit lookup_builtin_function_sig; eauto. intros EQ; subst sg. *)
(*   apply known_builtin_ok. *)
(* - apply external_functions_properties. *)
(* Qed. *)

(** Combining the semantics given above for the various kinds of external calls,
  we define the predicate [external_call] that relates:
- the external function being invoked
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).

This predicate is used in the semantics of all CompCert languages. *)

Definition external_call (ef: external_function): extcall_sem :=
  match ef with
  | EF_external name sg  => external_functions_sem name sg
  | EF_builtin name sg   => builtin_or_external_sem name sg
  | EF_runtime name sg   => builtin_or_external_sem name sg
  | EF_vload chunk       => volatile_load_sem chunk
  | EF_vstore chunk      => volatile_store_sem chunk
  | EF_malloc            => extcall_malloc_sem
  | EF_free              => extcall_free_sem
  | EF_memcpy sz al      => extcall_memcpy_sem sz al
  | EF_annot kind txt targs   => extcall_annot_sem txt targs
  | EF_annot_val kind txt targ => extcall_annot_val_sem txt targ
  | EF_inline_asm txt sg clb => inline_assembly_sem txt sg
  | EF_debug kind txt targs => extcall_debug_sem
  | EF_capture => extcall_capture_sem
  end.

Definition is_external_ef (ef: external_function): Prop :=
  match ef with
  | EF_external name sg  => True
  | EF_builtin name sg =>
    match lookup_builtin_function name sg with
    | Some bf => False
    | None => True
    end                    
  | EF_runtime name sg =>
    match lookup_builtin_function name sg with
    | Some bf => False
    | None => True
    end
  | EF_vload chunk => True
  | EF_inline_asm txt sg clb => True
  | EF_capture => True
  | _ => False
  end.

Definition is_external_efb (ef: external_function): bool :=
  match ef with
  | EF_external name sg  => true
  | EF_builtin name sg =>
    match lookup_builtin_function name sg with
    | Some bf => false
    | None => true
    end                    
  | EF_runtime name sg =>
    match lookup_builtin_function name sg with
    | Some bf => false
    | None => true
    end
  | EF_vload chunk => true
  | EF_inline_asm txt sg clb => true
  | EF_capture => true
  | _ => false
  end.

Lemma is_external_ef_reflect ef :
  reflect (is_external_ef ef) (is_external_efb ef).
Proof.
  destruct ef; ss; des_ifs; econs; eauto.
Qed.

Section BACKWARD_EXTCALL.

Variable ef: external_function.
Hypothesis IS_EXT: is_external_ef ef.

Theorem external_call_spec_backward:
   extcall_properties_backward (external_call ef) (ef_sig ef).
Proof.
 intros. unfold external_call, ef_sig. destruct ef; des_ifs.
 - apply external_functions_properties.
 - unfold builtin_or_external_sem. ss. des_ifs.
   apply external_functions_properties.
 - unfold builtin_or_external_sem. ss. des_ifs.
   apply external_functions_properties.
 - apply volatile_load_ok.
 - apply inline_assembly_properties.
 - apply extcall_capture_ok.
Qed.

Definition external_call_mem_extends_backward := ec_mem_extends_backward (external_call_spec_backward).
Definition external_call_mem_extends_backward_progress := ec_mem_extends_backward_progress (external_call_spec_backward).
Definition external_call_mem_inject_gen_backward := ec_mem_inject_backward (external_call_spec_backward).
Definition external_call_mem_inject_gen_backward_progress := ec_mem_inject_backward_progress (external_call_spec_backward).

End BACKWARD_EXTCALL.

Section FORWARD_EXTCALL.

Variable ef: external_function.
Hypothesis NOT_EXT: ~ is_external_ef ef.

Theorem external_call_spec:
  extcall_properties (external_call ef) (ef_sig ef).
Proof.
  intros. unfold external_call, ef_sig; destruct ef; ss.
  unfold builtin_or_external_sem. des_ifs.
  exploit lookup_builtin_function_sig; eauto. intros EQ; subst sg.
  eapply known_builtin_ok.
  unfold builtin_or_external_sem. des_ifs.
  exploit lookup_builtin_function_sig; eauto. intros EQ; subst sg.
  eapply known_builtin_ok.
  (* apply volatile_load_ok. *)
  apply volatile_store_ok.
  apply extcall_malloc_ok.
  apply extcall_free_ok.
  apply extcall_memcpy_ok.
  apply extcall_annot_ok.
  apply extcall_annot_val_ok.
  apply extcall_debug_ok.
Qed.

Definition external_call_mem_extends := ec_mem_extends (external_call_spec).
Definition external_call_mem_inject_gen := ec_mem_inject (external_call_spec).
Definition external_call_receptive := ec_receptive (external_call_spec).
Definition external_call_determ := ec_determ (external_call_spec).

End FORWARD_EXTCALL.

Theorem external_call_common_spec:
   forall ef,
   extcall_properties_common (external_call ef) (ef_sig ef).
Proof.
 intros. unfold external_call, ef_sig; destruct ef.
 apply external_functions_properties.
 unfold builtin_or_external_sem. des_ifs.
 exploit lookup_builtin_function_sig; eauto. intros EQ; subst sg.
 eapply known_builtin_ok. 
 apply external_functions_properties.
 unfold builtin_or_external_sem. des_ifs.
 exploit lookup_builtin_function_sig; eauto. intros EQ; subst sg.
 eapply known_builtin_ok.
 apply external_functions_properties.
 apply volatile_load_ok.
 apply volatile_store_ok.
 apply extcall_malloc_ok.
 apply extcall_free_ok.
 apply extcall_memcpy_ok.
 apply extcall_annot_ok.
 apply extcall_annot_val_ok.
 apply inline_assembly_properties.
 apply extcall_debug_ok.
 apply extcall_capture_ok.
Qed.

Definition external_call_well_typed_gen ef := ec_well_typed (external_call_common_spec ef).
Definition external_call_symbols_preserved ef := ec_symbols_preserved (external_call_common_spec ef).
Definition external_call_valid_block ef := ec_valid_block (external_call_common_spec ef).
Definition external_call_max_perm ef := ec_max_perm (external_call_common_spec ef).
Definition external_call_readonly ef := ec_readonly (external_call_common_spec ef).
(* Definition external_call_trace_length ef := ec_trace_length (external_call_common_spec ef). *)

Definition determ_properties (ef: external_function) := extcall_properties (external_call ef) (ef_sig ef).

(** Corollary of [external_call_well_typed_gen]. *)

Lemma external_call_well_typed:
  forall ef ge vargs m1 t vres m2,
  external_call ef ge vargs m1 t vres m2 ->
  Val.has_type vres (proj_sig_res (ef_sig ef)).
Proof.
  intros. apply Val.has_proj_rettype. eapply external_call_well_typed_gen; eauto.
Qed.

(** Corollary of [external_call_valid_block]. *)

Lemma external_call_nextblock:
  forall ef ge vargs m1 t vres m2,
  external_call ef ge vargs m1 t vres m2 ->
  Ple (Mem.nextblock m1) (Mem.nextblock m2).
Proof.
  intros. destruct (plt (Mem.nextblock m2) (Mem.nextblock m1)).
  exploit external_call_valid_block; eauto. intros.
  eelim Plt_strict; eauto.
  unfold Plt, Ple in *; zify; lia.
Qed.

(** Special case of [external_call_mem_inject_gen] (for backward compatibility) *)

Definition meminj_preserves_globals (F V: Type) (ge: Genv.t F V) (f: block -> option (block * Z)) : Prop :=
     (forall id b, Genv.find_symbol ge id = Some b -> f b = Some(b, 0))
  /\ (forall b gv, Genv.find_var_info ge b = Some gv -> f b = Some(b, 0))
  /\ (forall b1 b2 delta gv, Genv.find_var_info ge b2 = Some gv -> f b1 = Some(b2, delta) -> b2 = b1).

Lemma meminj_preserves_globals_to_symbols_inject
    F V (ge: Genv.t F V) f
    (GENV : meminj_preserves_globals ge f) :
  symbols_inject f ge ge.
Proof.
  destruct GENV as (A & B & C).
  repeat split; intros.
  + simpl in H0. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H0. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H0. exists b1; split; eauto.
  + simpl; unfold Genv.block_is_volatile.
    destruct (Genv.find_var_info ge b1) as [gv1|] eqn:V1.
    * exploit B; eauto. intros EQ; rewrite EQ in H; inv H. rewrite V1; auto.
    * destruct (Genv.find_var_info ge b2) as [gv2|] eqn:V2; auto.
      exploit C; eauto. intros EQ; subst b2. congruence.
Qed.

Lemma external_call_mem_inject_backward:
  forall ef F V (ge: Genv.t F V) vargs' m1' t vres' m2' f m1 vargs,
  is_external_ef ef ->
  meminj_preserves_globals ge f ->
  external_call ef ge vargs' m1' t vres' m2' ->
  Mem.inject f m1 m1' ->
  Val.inject_list f vargs vargs' ->
  (exists f', exists vres, exists m2,
     external_call ef ge vargs m1 t vres m2
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1')
  \/ (forall t' vres m2, ~ external_call ef ge vargs m1 t' vres m2)
  \/ ((~ trace_intact t) /\
     exists t' vres1 m21, external_call ef ge vargs m1 t' vres1 m21 /\
                     (exists tl, t' = (trace_cut_pterm t) ** tl)).
Proof.
  intros until vargs. intros EXT GENV TGTCALL MEM ARGS.
  destruct GENV as (A & B & C). exploit external_call_mem_inject_gen_backward; eauto.
  repeat split; intros.
  + simpl in H0. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H0. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H0. exists b1; split; eauto.
  + simpl; unfold Genv.block_is_volatile.
    destruct (Genv.find_var_info ge b1) as [gv1|] eqn:V1.
    * exploit B; eauto. intros EQ; rewrite EQ in H; inv H. rewrite V1; auto.
    * destruct (Genv.find_var_info ge b2) as [gv2|] eqn:V2; auto.
      exploit C; eauto. intros EQ; subst b2. congruence.
Qed.

Lemma external_call_mem_inject_backward_progress:
    forall ef F V (ge: Genv.t F V) vargs' m1' t vres m2 f m1 vargs,
    is_external_ef ef ->
    meminj_preserves_globals ge f ->
    external_call ef ge vargs m1 t vres m2 ->
    Mem.inject f m1 m1' ->
    Val.inject_list f vargs vargs' ->
    exists t' vres' m2',
      external_call ef ge vargs' m1' t' vres' m2'.
Proof.
  intros until vargs. intros EXT GENV SRCCALL MEM ARGS.
  destruct GENV as (A & B & C). eapply external_call_mem_inject_gen_backward_progress with (ge1:= ge); eauto. 
  repeat split; intros.
  + simpl in H0. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H0. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H0. exists b1; split; eauto.
  + simpl; unfold Genv.block_is_volatile.
    destruct (Genv.find_var_info ge b1) as [gv1|] eqn:V1.
    * exploit B; eauto. intros EQ; rewrite EQ in H; inv H. rewrite V1; auto.
    * destruct (Genv.find_var_info ge b2) as [gv2|] eqn:V2; auto.
      exploit C; eauto. intros EQ; subst b2. congruence.
Qed.

Lemma external_call_mem_inject:
  forall ef F V (ge: Genv.t F V) vargs m1 t vres m2 f m1' vargs' (DETERM: determ_properties ef),
  meminj_preserves_globals ge f ->
  external_call ef ge vargs m1 t vres m2 ->
  Mem.inject f m1 m1' ->
  Val.inject_list f vargs vargs' ->
  exists f', exists vres', exists m2',
     external_call ef ge vargs' m1' t vres' m2'
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1'.
Proof.
  intros. destruct H as (A & B & C). eapply ec_mem_inject with (ge1 := ge); eauto.
  repeat split; intros.
  + simpl in H3. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H3. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H3. exists b1; split; eauto.
  + simpl; unfold Genv.block_is_volatile.
    destruct (Genv.find_var_info ge b1) as [gv1|] eqn:V1.
    * exploit B; eauto. intros EQ; rewrite EQ in H; inv H. rewrite V1; auto.
    * destruct (Genv.find_var_info ge b2) as [gv2|] eqn:V2; auto.
      exploit C; eauto. intros EQ; subst b2. congruence.
Qed.

(** Corollaries of [external_call_determ]. *)

Lemma external_call_match_traces:
  forall ef ge vargs m t1 vres1 m1 t2 vres2 m2 (INT: ~ is_external_ef ef),
  external_call ef ge vargs m t1 vres1 m1 ->
  external_call ef ge vargs m t2 vres2 m2 ->
  t1 = t2.
Proof.
  intros. exploit external_call_determ. eauto. eexact H. eexact H0. tauto.
Qed.

Lemma external_call_deterministic:
  forall ef ge vargs m t vres1 m1 vres2 m2 (INT: ~ is_external_ef ef),
  external_call ef ge vargs m t vres1 m1 ->
  external_call ef ge vargs m t vres2 m2 ->
  vres1 = vres2 /\ m1 = m2.
Proof.
  intros. exploit external_call_determ. eauto. eexact H. eexact H0. intuition.
Qed.

Lemma external_call_trace_length
    ef ge vargs m t vres m1
    (INT: ~ is_external_ef ef)
    (EC: external_call ef ge vargs m t vres m1):
  (length t <= 1)%nat.
Proof. i. eapply external_call_spec in INT. inv INT. eauto. Qed.

(** * Evaluation of builtin arguments *)

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
      Mem.loadv chunk m (Val.offset_ptr sp ofs) = Some v ->
      eval_builtin_arg (BA_loadstack chunk ofs) v
  | eval_BA_addrstack: forall ofs,
      eval_builtin_arg (BA_addrstack ofs) (Val.offset_ptr sp ofs)
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

Global Hint Constructors eval_builtin_arg: barg.

(** Invariance by change of global environment. *)

Section EVAL_BUILTIN_ARG_PRESERVED.

Variables A F1 V1 F2 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma eval_builtin_arg_preserved:
  forall a v, eval_builtin_arg ge1 e sp m a v -> eval_builtin_arg ge2 e sp m a v.
Proof.
  assert (EQ: forall id ofs, Senv.symbol_address ge2 id ofs = Senv.symbol_address ge1 id ofs).
  { unfold Senv.symbol_address; simpl; intros. rewrite symbols_preserved; auto. }
  induction 1; eauto with barg. rewrite <- EQ in H; eauto with barg. rewrite <- EQ; eauto with barg.
Qed.

Lemma eval_builtin_args_preserved:
  forall al vl, eval_builtin_args ge1 e sp m al vl -> eval_builtin_args ge2 e sp m al vl.
Proof.
  induction 1; constructor; auto; eapply eval_builtin_arg_preserved; eauto.
Qed.

End EVAL_BUILTIN_ARG_PRESERVED.

(** Compatibility with the "is less defined than" relation. *)

Section EVAL_BUILTIN_ARG_LESSDEF.

Variable A: Type.
Variable ge: Senv.t.
Variables e1 e2: A -> val.
Variable sp: val.
Variables m1 m2: mem.

Hypothesis env_lessdef: forall x, Val.lessdef (e1 x) (e2 x).
Hypothesis mem_extends: Mem.extends m1 m2.

Lemma eval_builtin_arg_lessdef:
  forall a v1, eval_builtin_arg ge e1 sp m1 a v1 ->
  exists v2, eval_builtin_arg ge e2 sp m2 a v2 /\ Val.lessdef v1 v2.
Proof.
  induction 1.
- exists (e2 x); auto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_extends; eauto. intros (v' & P & Q). exists v'; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_extends; eauto. intros (v' & P & Q). exists v'; eauto with barg.
- econstructor; eauto with barg.
- destruct IHeval_builtin_arg1 as (vhi' & P & Q).
  destruct IHeval_builtin_arg2 as (vlo' & R & S).
  econstructor; split; eauto with barg. apply Val.longofwords_lessdef; auto.
- destruct IHeval_builtin_arg1 as (vhi' & P & Q).
  destruct IHeval_builtin_arg2 as (vlo' & R & S).
  econstructor; split; eauto with barg. 
  destruct Archi.ptr64; auto using Val.add_lessdef, Val.addl_lessdef.
Qed.

Lemma eval_builtin_args_lessdef:
  forall al vl1, eval_builtin_args ge e1 sp m1 al vl1 ->
  exists vl2, eval_builtin_args ge e2 sp m2 al vl2 /\ Val.lessdef_list vl1 vl2.
Proof.
  induction 1.
- econstructor; split. constructor. auto.
- exploit eval_builtin_arg_lessdef; eauto. intros (v1' & P & Q).
  destruct IHlist_forall2 as (vl' & U & V).
  exists (v1'::vl'); split; constructor; auto.
Qed.

End EVAL_BUILTIN_ARG_LESSDEF.

Section ExtcallPropImply.

(** Extcall properties : relaxed *)

Lemma forwrard_axiom_implies_backward_axiom
    sem sg
    (FORWARD: extcall_properties sem sg) :
  extcall_properties_backward sem sg.
Proof.
  econstructor; inv FORWARD; eauto; i.
  - destruct (classic (exists t' vres m2, sem ge vargs m1 t' vres m2)); cycle 1.
    { right. left. red. ii. eapply H; eauto. }
    destruct H as [t' [vres [m2 H]]].
    left. exploit ec_mem_extends0; eauto. i. des.
    exploit ec_determ0. eapply H0. eapply CALLTGT. intros (TRC & TRC').
    des; subst. esplits; eauto.
  - exploit ec_mem_extends0; eauto. i. des; eauto.
  - destruct (classic (exists t' vres m2, sem ge1 vargs m1 t' vres m2)); cycle 1.
    { right. left. ii. eapply H; eauto. }
    destruct H as [t' [vres [m2 H]]]. left. exploit ec_mem_inject0; eauto.
    i. des. exploit ec_determ0. eapply H0. eapply CALLTGT. intros (TRC & TRC').
    des; subst. esplits; eauto.
  - intros. exploit ec_mem_inject0; eauto. i. des; eauto.
  - intros. exploit ec_mem_inject0; eauto. i. des.
    exploit ec_determ0. eapply CALLSRC. eauto. intros. des; subst.
    esplits; eauto.
  - destruct (classic (exists t' vres m2, sem ge vargs m1 t' vres m2)); cycle 1.
    { right. left. ii. eapply H2; eauto. }
    destruct H2 as [t [vres [m2 H2]]].
    left. exploit ec_mem_concrete_extends0; eauto. i. des.
    exploit ec_determ0. eapply H4. eapply H. i; des; subst. esplits; eauto.
  - i. exploit ec_mem_concrete_extends0; eauto. i. des; eauto.
Qed.

End ExtcallPropImply.

Lemma ge_binded_store ge m gm chunk b ofs v m'
    (BIND: ge_binded ge m gm)
    (STORE: Mem.store chunk m b ofs v = Some m'):
  ge_binded ge m' gm.
Proof.
  unfold ge_binded in *. i. exploit BIND; eauto. i. des.
  split; eauto. rewrite <- H1. erewrite <-Mem.concrete_store; eauto.
Qed.

Lemma ge_binded_alloc ge m gm lo hi m' v
    (BIND: ge_binded ge m gm)
    (ALLOC: Mem.alloc m lo hi = (m', v)):
  ge_binded ge m' gm.
Proof.
  unfold ge_binded in *. i. exploit BIND; eauto. i. des.
  split; eauto. rewrite <- H1. erewrite <-Mem.concrete_alloc; eauto.
Qed.

Lemma ge_binded_free ge m gm v lo hi m'
    (BIND: ge_binded ge m gm)
    (FREE: Mem.free m v lo hi = Some m'):
  ge_binded ge m' gm.
Proof.
  unfold ge_binded in *. i. exploit BIND; eauto. i. des.
  split; eauto. rewrite <- H1. erewrite <-Mem.concrete_free; eauto.
Qed.

Lemma ge_binded_external_call ge m gm ef vargs t vres m'
    (BIND: ge_binded ge m gm)
    (EXT: external_call ef ge vargs m t vres m'):
  ge_binded ge m' gm.
Proof.
  unfold ge_binded in *. i. exploit BIND; eauto. i. des.
  split; eauto. rewrite H2 in *. eapply ec_binds; eauto. eapply external_call_common_spec.
Qed.

Lemma ge_binded_senv_equiv ge tge m gm
    (SEQ: Senv.equiv ge tge):
  ge_binded ge m gm <-> ge_binded tge m gm.
Proof.
  inv SEQ. inv H0. split; ii.
  - eapply H0; eauto. rewrite <- H; eauto.
  - eapply H0; eauto. rewrite H; eauto.
Qed.

