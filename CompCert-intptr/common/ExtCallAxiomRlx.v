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
Require Import Events.

Section RLX.

Record extcall_properties_common_old (sem: extcall_sem) (sg: signature) : Prop :=
  mk_extcall_properties_common_old {
  
(** The return value of an external call must agree with its signature. *)
  ec_well_typed_old:
    forall ge vargs m1 t vres m2,
    sem ge vargs m1 t vres m2 ->
    Val.has_rettype vres sg.(sig_res);

(** The semantics is invariant under change of global environment that preserves symbols. *)
  ec_symbols_preserved_old:
    forall ge1 ge2 vargs m1 t vres m2,
    Senv.equiv ge1 ge2 ->
    sem ge1 vargs m1 t vres m2 ->
    sem ge2 vargs m1 t vres m2;

(** External calls cannot invalidate memory blocks.  (Remember that
  freeing a block does not invalidate its block identifier.) *)
  ec_valid_block_old:
    forall ge vargs m1 t vres m2 b,
    sem ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.valid_block m2 b;

(** External calls cannot increase the max permissions of a valid block.
    They can decrease the max permissions, e.g. by freeing. *)
  ec_max_perm_old:
    forall ge vargs m1 t vres m2 b ofs p,
    sem ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p;

(** External call cannot modify memory unless they have [Max, Writable]
   permissions. *)
  ec_readonly_old:
    forall ge vargs m1 t vres m2 b ofs n bytes,
    sem ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b ->
    Mem.loadbytes m2 b ofs n = Some bytes ->
    (forall i, ofs <= i < ofs + n -> ~Mem.perm m1 b i Max Writable) ->
    Mem.loadbytes m1 b ofs n = Some bytes;
}.

(* old forward version of extcall properties *)
Record extcall_properties_old (sem: extcall_sem) (sg: signature) : Prop :=
  mk_extcall_properties_old {

  ec_properties_old_common:
    extcall_properties_common_old sem sg;

(** External calls produce at most one event. *)
  ec_trace_length_old:
    forall ge vargs m t vres m',
    sem ge vargs m t vres m' -> (length t <= 1)%nat;
      
(** External calls must commute with memory extensions, in the
  following sense. *)
  ec_mem_extends_old:
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
  ec_mem_inject_old:
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

(** External calls must be receptive to changes of traces by another, matching trace. *)
  ec_receptive_old:
    forall ge vargs m t1 vres1 m1 t2,
    sem ge vargs m t1 vres1 m1 -> match_traces ge t1 t2 ->
    exists vres2, exists m2, sem ge vargs m t2 vres2 m2;

(** External calls must be deterministic up to matching between traces. *)
  ec_determ_old:
    forall ge vargs m t1 vres1 m1 t2 vres2 m2,
    sem ge vargs m t1 vres1 m1 -> sem ge vargs m t2 vres2 m2 ->
    match_traces ge t1 t2 /\ (t1 = t2 -> vres1 = vres2 /\ m1 = m2);
}.

(* backward version of extcall properties: *)
(* Its subset of our axiom. *the first two changes* of external call axiom in 4.1.2 *)
Record extcall_properties_backward_sim (sem: extcall_sem) (sg: signature) : Prop :=
  mk_extcall_properties_backward_sim {

  ec_properties_backward_common_sim:
    extcall_properties_common_old sem sg;

(** External calls must commute with memory extensions, in the
  following sense. *)
  ec_mem_extends_backward_sim
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

  ec_mem_extends_backward_progress_sim
    ge vargs m1 t vres m2 m1' vargs'
    (CALLSRC: sem ge vargs m1 t vres m2)
    (MEM: Mem.extends m1 m1')
    (ARGS: Val.lessdef_list vargs vargs') :
    (exists t' vres' m2',
      <<CALLTGT: sem ge vargs' m1' t' vres' m2'>>);

(** External calls must commute with memory injections,
  in the following sense. *)
  ec_mem_inject_backward_sim
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

  ec_mem_inject_backward_progress_sim
    ge1 ge2 vargs m1 t vres m2 f m1' vargs'
    (SYMB: symbols_inject f ge1 ge2)
    (CALLSRC: sem ge1 vargs m1 t vres m2)
    (MEM: Mem.inject f m1 m1')
    (ARGS: Val.inject_list f vargs vargs') :
    (exists t'' vres' m2',
      <<CALLTGT: sem ge2 vargs' m1' t'' vres' m2'>>);

  ec_sound_sim
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
}.

Lemma forwrard_axiom_implies_backward_axiom_sim
      sem sg
      (FORWARD: extcall_properties_old sem sg) :
  extcall_properties_backward_sim sem sg.
Proof.
  econstructor; inv FORWARD; eauto.
  - intros.
    destruct (classic (exists t' vres m2, sem ge vargs m1 t' vres m2)); cycle 1.
    { right. left. red. ii. eapply H; eauto. }
    destruct H as [t' [vres [m2 H]]].
    left. exploit ec_mem_extends_old0; eauto. intros (vres'0 & m2'0 & SEM & VAL & MEXT & NOCHANGE).
    exploit ec_determ_old0. eapply SEM. eapply CALLTGT. intros (TRC & TRC').
    exploit ec_receptive_old0. eapply H. eauto. intros (vres2 & m3 & SEM').
    exploit ec_mem_extends_old0. eapply SEM'. eauto. eauto.
    intros (vres'1 & m2'1 & SEM'' & VAL' & MEXT' & NOCHANGE').
    exploit ec_determ_old0. eapply CALLTGT. eauto. intros (TRC1 & TRC1').
    exploit TRC1'; eauto. intros [A B]. subst.
    do 2 eexists. repeat (split; eauto).
  - intros. exploit ec_mem_extends_old0; eauto. intros (vres' & m2' & A & B & C & D).
    do 3 eexists. eauto.
  - intros.
    destruct (classic (exists t' vres m2, sem ge1 vargs m1 t' vres m2)); cycle 1.
    { right. left. ii. eapply H; eauto. }
    destruct H as [t' [vres [m2 H]]].
    left. exploit ec_mem_inject_old0; eauto.
    intros (f' & vres'0 & m2'0 & SEM & VAL & MEXT & NOCHANGE).
    exploit ec_determ_old0. eapply SEM. eapply CALLTGT. intros (TRC & TRC').
    exploit ec_receptive_old0. eapply H. eapply match_traces_preserved.
    instantiate (1:=ge2). unfold symbols_inject in *. inv SYMB. eauto. eauto.
    intros (vres2 & m3 & SEM').
    exploit ec_mem_inject_old0; eauto.
    intros (f'0 & vres'1 & m2'1 & SEM1 & VAL1 & MEXT1 & NOCHANGE1).
    exploit ec_determ_old0. eapply CALLTGT. eauto. intros (TRC1 & TRC1').
    exploit TRC1'; eauto. intros [A B]. subst.
    do 3 eexists. repeat (split; eauto).
  - intros. exploit ec_mem_inject_old0; eauto.
    intros (f' & vres' & m2' & A & B). eauto.
  - intros. exploit ec_mem_inject_old0; eauto.
    intros (f' & vres' & m2' & A & B & C & D & E & F & G).
    exploit ec_determ_old0. eapply CALLSRC. eauto. intros. inv H.
    exploit H1; eauto. intros [A' B']. subst.
    eexists. repeat (split; eauto).
Qed.

End RLX.
