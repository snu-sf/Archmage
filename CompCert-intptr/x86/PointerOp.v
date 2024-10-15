Require Import BoolEqual.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Maps.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
(* Require Import Cminor. *)
Require Import Op.
Require Import IntPtrRel.
Require Import sflib Classical.

Set Implicit Arguments.

(* unary cmp *)
Definition ptr_uncond (c: condition) : bool :=
  match c with
  | Ccompuimm _ _ => if negb Archi.ptr64 then true else false
  | Ccompluimm _ _ => if Archi.ptr64 then true else false
  | _ => false
  end.

Definition ptr_bincond (c: condition) : bool :=
  match c with
  | Ccompu _ => if negb Archi.ptr64 then true else false
  | Ccomplu _ => if Archi.ptr64 then true else false
  | _ => false
  end.
      
Definition ptr_cond (c: condition) : bool :=
  orb (ptr_uncond c) (ptr_bincond c).

Definition ptr_binop (op: operation) : bool :=
  match op with
  | Ocmp c => ptr_cond c
  | Opsub =>  true
  | _ => false
  end.

Definition ptr_op (op: operation) : bool :=
  match op with
  | Osel c _ => ptr_cond c
  | _ => ptr_binop op
  end.

(* Osel needs this *)
Definition eval_condition_join (c: condition) (vl: list val) (m: mem) : option bool :=
  match c with
  | Ccompuimm cmp n => match vl with
                      | [] => None
                      | [v] => cmpu_join_common m cmp v (Vint n) 
                      | _ => None
                      end
  | Ccompluimm cmp n => match vl with
                       | [] => None
                       | [v] => cmplu_join_common m cmp v (Vlong n) 
                       | _ => None
                       end
  | Ccomplu cmp => match vl with
                  | [] => None
                  | [v] => None
                  | [v1; v2] => cmplu_join_common m cmp v1 v2
                  | _ => None
                  end
  | Ccompu cmp => match vl with
                 | [] => None
                 | [v] => None
                 | [v1; v2] => cmpu_join_common m cmp v1 v2
                 | _ => None
                 end
  | _ => None
  end.

(* TODO: check Archi.ptr64 first *)
Definition cmplu_bool_join_asm (m: mem) (cmp: comparison) (v1 v2: val) : option bool :=
  cmplu_join_common m cmp v1 v2.

Definition cmplu_join_asm (m: mem) (cmp: comparison) (v1 v2: val) : option val :=
  option_map Val.of_bool (cmplu_bool_join_asm m cmp v1 v2).

Lemma cmplu_join_same_eval_condition_join c v1 v2 m :
  cmplu_bool_join_asm m c v1 v2 = eval_condition_join (Ccomplu c) [v1; v2] m.
Proof. ss. Qed.

Lemma cmplu_join_same_eval_condition_join_imm c v n m:
  cmplu_bool_join_asm m c v (Vlong n) = eval_condition_join (Ccompluimm c n) [v] m.
Proof. ss. Qed.

Definition eval_condition_wrapper (c: condition) (vl: list val) (m: mem) : option bool :=
  if ptr_cond c then eval_condition_join c vl m else eval_condition c vl m.

Definition eval_operation_join (F V: Type) (genv: Genv.t F V) (sp: val)
  (op: operation) (vl: list val) (m: mem): option val :=
  match op with
  | Ocmp c => Some (Val.of_optbool (eval_condition_join c vl m))
  | Opsub => match vl with
            | [] => None
            | [v] => None
            | [v1; v2] => if Archi.ptr64
                         then Some (psubl_join_common m v1 v2)
                         else Some (psub_join_common m v1 v2)
            | _ => None
            end
  | _ => None
  end.

Definition psub_join_asm (m: mem) (v1 v2: val) : val :=
  if Archi.ptr64
  then psubl_join_common m v1 v2
  else psub_join_common m v1 v2.

Definition eval_operation_wrapper (F V: Type) (genv: Genv.t F V) (sp: val)
  (op: operation) (vl: list val) (m: mem): option val :=
  if ptr_op op
  then
    match op with
    | Osel c ty => match vl with
                  | [] => None
                  | [v1] => None
                  | v1 :: v2 :: vl0 => Some (Val.select (eval_condition_join c vl0 m) v1 v2 ty)
                  end
    | _ => eval_operation_join genv sp op vl m
    end
  else
    eval_operation genv sp op vl m.


Lemma  eval_condition_no_ptr_op c vl m
    (NOPTR: ptr_cond c = false) :
  <<SAME: eval_condition_wrapper c vl m = eval_condition c vl m>>.
Proof. unfold eval_condition_wrapper. rewrite NOPTR. eauto. Qed.

Lemma eval_operation_no_ptr_op F V (genv: Genv.t F V) sp op vl m
    (NOPTR: ptr_op op = false) :
  <<SAME: eval_operation_wrapper genv sp op vl m = eval_operation genv sp op vl m>>.
Proof. unfold eval_operation_wrapper. rewrite NOPTR. eauto. Qed.

Section GENV_TRANSF.

Variable F1 F2 V1 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.

Hypothesis agree_on_symbols:
  forall (s: ident), Genv.find_symbol ge2 s = Genv.find_symbol ge1 s.

Lemma eval_operation_wrapper_preserved:
  forall sp op vl m,
  eval_operation_wrapper ge2 sp op vl m = eval_operation_wrapper ge1 sp op vl m.
Proof. intros. unfold eval_operation_wrapper. erewrite eval_operation_preserved; eauto. Qed.

End GENV_TRANSF.

Lemma eval_condition_no_angelic
    cond m vl bp bi
    (PTRCOND: ptr_bincond cond = true)
    (COND1: eval_condition cond (map (to_ptr_val m) vl) m = Some bp)
    (COND2: eval_condition cond (map (to_int_val m) vl) m = Some bi) :
  <<NOANGELIC: bp = bi>>.
Proof.
  destruct (Archi.ptr64) eqn:BIT.
  - destruct cond; simpl in *; try rewrite BIT in *; simpl in *; inv PTRCOND.
    do 2 (destruct vl; [ss|]). destruct vl; [|ss]. simpl in *.
    eapply cmplu_no_angelic; eauto.
  - destruct cond; simpl in *; try rewrite BIT in *; simpl in *; inv PTRCOND.
    do 2 (destruct vl; [ss|]). destruct vl; [|ss]. simpl in *.
    eapply cmpu_no_angelic; eauto.
Qed.

Lemma cmp_wrapper_eval_condition_join
    F V (genv: Genv.t F V) sp c vl m
    (PTRCOND: ptr_cond c = true) :
  <<SAME: eval_operation_wrapper genv sp (Ocmp c) vl m = Some (Val.of_optbool (eval_condition_join c vl m))>>.
Proof.
  unfold eval_operation_wrapper. simpl. rewrite PTRCOND. eauto.
Qed.

Definition not_cmp (op: operation) : bool :=
  match op with
  | Ocmp _ => false
  | _ => true
  end.

Lemma eval_operation_join_no_angelic
    F V (genv: Genv.t F V) sp op vl m vp vi
    (PTROP: ptr_binop op = true)
    (NOCMP: not_cmp op = true)
    (EVAL1: eval_operation genv sp op (map (to_ptr_val m) vl) m = Some vp)
    (EVAL2: eval_operation genv sp op (map (to_int_val m) vl) m = Some vi) :
  <<NOANGELIC: vp = Vundef \/ vi = Vundef \/ vi = vp>>.
Proof.
  destruct (Archi.ptr64) eqn:BIT.
  - destruct op; simpl in *; try rewrite BIT in *; inv PTROP; [|clarify].
    do 2 (destruct vl; [ss|]). destruct vl; [|ss]. simpl in *.
    inv EVAL1; inv EVAL2. eapply psubl_wrapper_no_angelic; eauto.
  - destruct op; simpl in *; try rewrite BIT in *; inv PTROP; [|clarify].
    do 2 (destruct vl; [ss|]). destruct vl; [|ss]. simpl in *.
    inv EVAL1; inv EVAL2. eapply psub_wrapper_no_angelic; eauto.
Qed.

Lemma negate_cmpu_join c v1 v2 m:
  <<SAME: cmpu_join m (negate_comparison c) v1 v2 = option_map negb (cmpu_join m c v1 v2)>>.
Proof.
  unfold cmpu_join. do 2 rewrite Val.negate_cmpu_bool. unfold bool_optjoin, opt_join.
  des_ifs. simpl in *. inv Heq; inv Heq0. destruct b1; destruct b2; ss.
Qed.

Lemma negate_cmplu_join c v1 v2 m:
  <<SAME: cmplu_join m (negate_comparison c) v1 v2 = option_map negb (cmplu_join m c v1 v2)>>.
Proof.
  unfold cmplu_join. do 2 rewrite Val.negate_cmplu_bool. unfold bool_optjoin, opt_join.
  des_ifs. simpl in *. inv Heq; inv Heq0. destruct b1; destruct b2; ss.
Qed.

Lemma eval_negate_condition_join cond vl m (PTRCOND: ptr_cond cond = true) :
  <<SAME: eval_condition_join (negate_condition cond) vl m = option_map negb (eval_condition_join cond vl m)>>.
Proof.
  destruct Archi.ptr64 eqn:SF.
  - unfold eval_condition_join, ptr_cond, cmplu_join_common in *.
    destruct cond; simpl in *; try rewrite SF in *; inv PTRCOND.
    + repeat (destruct vl; auto). simpl. repeat rewrite Val.negate_cmplu_bool;
      unfold bool_optjoin, opt_join; des_ifs; simpl in *; clarify;
        rewrite negate_cmplu_join; eauto.
    + repeat (destruct vl; auto). rewrite Val.negate_cmplu_bool; eauto.
      rewrite negate_cmplu_join; eauto. des_ifs.
  - unfold eval_condition_join, ptr_cond, cmpu_join_common in *.
    destruct cond; simpl in *; try rewrite SF in *; inv PTRCOND.
    + repeat (destruct vl; auto). simpl. repeat rewrite Val.negate_cmpu_bool;
      unfold bool_optjoin, opt_join; des_ifs; simpl in *; clarify;
        rewrite negate_cmpu_join; eauto.
    + repeat (destruct vl; auto). rewrite Val.negate_cmpu_bool; eauto.
      rewrite negate_cmpu_join; eauto. des_ifs.
Qed.

Lemma ptr_binop_not_shift_stack
    F V op (genv: Genv.t F V) sp1 vl m
    (PTROP: ptr_op op = true) delta :
  eval_operation genv (Vptr sp1 Ptrofs.zero) op vl m =
  eval_operation genv (Vptr sp1 Ptrofs.zero) (shift_stack_operation delta op) vl m.
Proof. unfold shift_stack_operation; ss. des_ifs. Qed.

Lemma ptr_binop_operation_to_ptr_return
    F V (genv: Genv.t F V) sp op vl m v
    (PTROP: ptr_binop op = true)
    (EVAL: eval_operation genv sp op vl m = Some v) :
  is_only_int v = true.
Proof.
  destruct op; ss.
  - des_ifs. destruct v0; destruct v1; ss; clarify; eauto; ss; unfold Val.psubl; des_ifs; eauto.
  - des_ifs. unfold eval_condition. des_ifs; ss; eauto. unfold Val.of_optbool. des_ifs; eauto.
    unfold Val.of_optbool. des_ifs; eauto.
Qed.

Lemma type_of_operation_wrapper_sound
    F V (genv: Genv.t F V) op vl sp v m
    (NOTMV: op <> Omove)
    (EVAL: eval_operation_wrapper genv sp op vl m = Some v) :
  <<SOUND: Val.has_type v (snd (type_of_operation op))>>.
Proof with (try exact I; try reflexivity).
  destruct (ptr_op op) eqn:PTROP.
  2:{ rewrite eval_operation_no_ptr_op in EVAL; eauto.
      eapply type_of_operation_sound; eauto. }
  destruct op; ss.
  - unfold eval_operation_wrapper, Tptr in *. simpl in *.
    destruct vl; [clarify|]. destruct vl; [clarify|]. destruct vl; [|clarify].
    destruct Archi.ptr64 eqn:SF.
  + destruct v0, v1; simpl in *; inv EVAL; simpl; auto.
  * rewrite SF. simpl; eauto.
  * unfold psubl_join.
    destruct (classic (Val.psubl (to_ptr_val m (Vlong i)) (to_ptr_val m (Vptr b i0)) = Vundef)).
    { destruct (classic (Val.psubl (to_int_val m (Vlong i)) (to_int_val m (Vptr b i0)) = Vundef)).
      { rewrite H, H0. simpl. eauto. }
      rewrite val_join_angelic_vi; try eapply H0.
      { unfold Val.psubl. des_ifs; eauto. }
      { unfold Val.psubl. des_ifs; eauto. }
      { eapply psubl_wrapper_no_angelic; eauto. } }
    rewrite val_join_angelic_vp; try eapply H.
    { unfold Val.psubl. des_ifs; eauto. }
    { unfold Val.psubl. des_ifs; eauto. }
    { eapply psubl_wrapper_no_angelic; eauto. }
  * unfold psubl_join.
    destruct (classic (Val.psubl (to_ptr_val m (Vptr b i)) (to_ptr_val m (Vlong i0)) = Vundef)).
    { destruct (classic (Val.psubl (to_int_val m (Vptr b i)) (to_int_val m (Vlong i0)) = Vundef)).
      { rewrite H, H0. simpl. eauto. }
      rewrite val_join_angelic_vi; try eapply H0.
      { unfold Val.psubl. des_ifs; eauto. }
      { unfold Val.psubl. des_ifs; eauto. }
      { eapply psubl_wrapper_no_angelic; eauto. } }
    rewrite val_join_angelic_vp; try eapply H.
    { unfold Val.psubl. des_ifs; eauto. }
    { unfold Val.psubl. des_ifs; eauto. }
    { eapply psubl_wrapper_no_angelic; eauto. }
  * rewrite SF. simpl. destruct (eq_block b b0); simpl; eauto.
  + destruct v0, v1; simpl in *; inv EVAL; simpl; auto.
  * rewrite SF. simpl; eauto.
  * unfold psub_join.
    destruct (classic (Val.psub (to_ptr_val m (Vint i)) (to_ptr_val m (Vptr b i0)) = Vundef)).
    { destruct (classic (Val.psub (to_int_val m (Vint i)) (to_int_val m (Vptr b i0)) = Vundef)).
      { rewrite H, H0. simpl. eauto. }
      rewrite val_join_angelic_vi; try eapply H0.
      { unfold Val.psubl. des_ifs; eauto. }
      { unfold Val.psubl. des_ifs; eauto. }
      { eapply psub_wrapper_no_angelic; eauto. } }
    rewrite val_join_angelic_vp; try eapply H.
    { unfold Val.psub. des_ifs; eauto. }
    { unfold Val.psub. des_ifs; eauto. }
    { eapply psub_wrapper_no_angelic; eauto. }
  * unfold psub_join.
    destruct (classic (Val.psub (to_ptr_val m (Vptr b i)) (to_ptr_val m (Vint i0)) = Vundef)).
    { destruct (classic (Val.psub (to_int_val m (Vptr b i)) (to_int_val m (Vint i0)) = Vundef)).
      { rewrite H, H0. simpl. eauto. }
      rewrite val_join_angelic_vi; try eapply H0.
      { unfold Val.psub. des_ifs; eauto. }
      { unfold Val.psub. des_ifs; eauto. }
      { eapply psub_wrapper_no_angelic; eauto. } }
    rewrite val_join_angelic_vp; try eapply H.
    { unfold Val.psub. des_ifs; eauto. }
    { unfold Val.psub. des_ifs; eauto. }
    { eapply psub_wrapper_no_angelic; eauto. }
  * rewrite SF. simpl. destruct (eq_block b b0); simpl; eauto.
  - unfold eval_operation_wrapper in EVAL. simpl in *.
    unfold Val.of_optbool in EVAL. des_ifs; ss.
  - unfold eval_operation_wrapper in EVAL; ss. 
    unfold Val.select in *. des_ifs; ss; eapply Val.normalize_type.
Qed.

Lemma negate_ptr_cond c:
  <<NEGC: ptr_cond c = ptr_cond (negate_condition c)>>.
Proof. destruct c; ss. Qed.

Lemma eval_negate_condition_wrapper cond vl m:
  <<NEGC: eval_condition_wrapper (negate_condition cond) vl m = option_map negb (eval_condition_wrapper cond vl m)>>.
Proof.
  destruct (ptr_cond cond) eqn:PCOND.
  2:{ repeat (erewrite eval_condition_no_ptr_op; eauto).
      - eapply eval_negate_condition.
      - rewrite <- negate_ptr_cond; eauto. }
  unfold eval_condition_wrapper. rewrite PCOND.
  rewrite negate_ptr_cond in PCOND. rewrite PCOND. 
  eapply eval_negate_condition_join. rewrite negate_ptr_cond. eauto.
Qed.

Lemma condition_wrapper_depends_on_memory_correct args m1 m2 c
    (INDEP: condition_depends_on_memory c = false) :
  <<SAME: eval_condition_wrapper c args m1 = eval_condition_wrapper c args m2>>.
Proof. destruct c; ss. Qed.

Lemma same_concrete_same_psubl_l m1 m2 n b ofs
    (SAMECONC: Mem.mem_concrete m1 = Mem.mem_concrete m2) :
  <<SAME: psubl_join m1 (Vlong n) (Vptr b ofs) = psubl_join m2 (Vlong n) (Vptr b ofs)>>.
Proof.
  destruct ((Mem.mem_concrete m1)!b) eqn:CONC1.
- erewrite psubl_always_captured1'; eauto.
  rewrite SAMECONC in CONC1. erewrite psubl_always_captured1'; eauto.
- rewrite psubl_always_captured1_undef; eauto.
  rewrite SAMECONC in CONC1. rewrite psubl_always_captured1_undef; eauto.
Qed.

Lemma same_concrete_same_psubl_r m1 m2 n b ofs
    (SAMECONC: Mem.mem_concrete m1 = Mem.mem_concrete m2) :
  <<SAME: psubl_join m1 (Vptr b ofs) (Vlong n) = psubl_join m2 (Vptr b ofs) (Vlong n)>>.
Proof.
  destruct ((Mem.mem_concrete m1)!b) eqn:CONC1.
- erewrite psubl_always_captured2'; eauto.
  rewrite SAMECONC in CONC1. erewrite psubl_always_captured2'; eauto.
- rewrite psubl_always_captured2_undef; eauto.
  rewrite SAMECONC in CONC1. rewrite psubl_always_captured2_undef; eauto.
Qed.
  
Lemma op_wrapper_depends_on_memory_correct
    (F V: Type) (ge: Genv.t F V) sp op args m1 m2
    (CONC: Mem.mem_concrete m1 = Mem.mem_concrete m2)
    (INDEP: op_depends_on_memory op = false) :
  <<SAME: eval_operation_wrapper ge sp op args m1 = eval_operation_wrapper ge sp op args m2>>.
Proof.
  destruct (ptr_op op) eqn:PTROP; cycle 1.
  { do 2 (rewrite eval_operation_no_ptr_op; eauto). 
    eapply op_depends_on_memory_correct; eauto. }
  destruct op; ss.
  - unfold eval_operation_wrapper. ss. unfold psubl_join_common, psub_join_common. des_ifs_safe.
    des_ifs; eauto.
    + erewrite same_concrete_same_psubl_l; eauto.
    + erewrite same_concrete_same_psubl_r; eauto.
  - destruct cond; ss.
  - destruct c; ss.
Qed.

Definition op_depends_on_both_memory (op: operation) : bool :=
  match op with
  | Opsub => true
  | _ => op_depends_on_memory op
  end.

Lemma op_wrapper_depends_on_both_memory_correct
    (F V: Type) (ge: Genv.t F V) sp op args m1 m2
    (INDEP: op_depends_on_both_memory op = false) :
  <<SAME: eval_operation_wrapper ge sp op args m1 = eval_operation_wrapper ge sp op args m2>>.
Proof.
  destruct (ptr_op op) eqn:PTROP; cycle 1.
  { do 2 (rewrite eval_operation_no_ptr_op; eauto). 
    eapply op_depends_on_memory_correct; eauto.
    destruct op; ss. }
  destruct op; ss; [destruct cond; ss| destruct c; ss].
Qed.

Section EVAL_COMPAT.

Variable F1 F2 V1 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.
Variable f: meminj.

Variable m1: mem.
Variable m2: mem.

Hypothesis mi_inj_perm: forall b1 b2 delta ofs k p,
    f b1 = Some (b2, delta) ->
    Mem.perm m1 b1 ofs k p -> Mem.perm m2 b2 (ofs + delta) k p.

Hypothesis valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_pointer_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.

Hypothesis weak_valid_pointer_no_overflow:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.

Hypothesis valid_different_pointers_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs1) = true ->
  Mem.valid_pointer m1 b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).

Hypothesis src_concrete_private: forall b, f b = None -> (Mem.mem_concrete m1) ! b = None.

Hypothesis mappedblocks: forall b b' delta, Mem.valid_block m1 b -> f b = Some (b', delta) -> Mem.valid_block m2 b'.

Hypothesis src_concrete_public: forall b1 b2 addr delta,
    f b1 = Some (b2, delta) ->
    (Mem.mem_concrete m1) ! b1 = Some addr ->
    (Mem.mem_concrete m2) ! b2 = Some (addr - delta).

Hypothesis representable: forall b b' delta ofs,
    f b = Some (b', delta) ->
    Mem.perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/
    Mem.perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
    delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned.

Lemma eval_condition_join_inj c vl1 vl2 b
    (PTRCOND: ptr_cond c = true)
    (VINJ: Val.inject_list f vl1 vl2)
    (EVAL: eval_condition_join c vl1 m1 = Some b) :
  <<EVAL': eval_condition_join c vl2 m2 = Some b>>.
Proof.
  unfold ptr_cond, ptr_uncond, ptr_bincond in PTRCOND.
  destruct Archi.ptr64 eqn:SF; simpl in *; destruct c; simpl in PTRCOND; inv PTRCOND; ss.
  (* cmplu *)
  - do 2 (destruct VINJ; [ss|]). destruct VINJ; [|ss]. dup H. dup H0. unfold eval_condition_join, cmplu_join_common.
    destruct v; destruct v0; inv H; inv H0; simpl in EVAL;
      try rewrite SF in *; simpl in EVAL; inv EVAL; eauto.
    + rewrite H0. destruct (Int64.eq i Int64.zero) eqn:NULL.
      { eapply Val.cmplu_bool_inject; eauto. simpl. rewrite SF, NULL. eauto. }
      { exploit cmplu_join_inj; try eapply H0; eauto. }
    + rewrite H0. destruct (Int64.eq i0 Int64.zero) eqn:NULL.
      { eapply Val.cmplu_bool_inject; eauto. simpl. rewrite SF, NULL. eauto. }
      { exploit cmplu_join_inj; try eapply H0; eauto. }
    + rewrite H0. eapply Val.cmplu_bool_inject; eauto.
  (* cmpluimm *)
  - destruct VINJ; [ss|]. destruct VINJ; [|ss]. dup H. unfold eval_condition_join, cmplu_join_common.
    destruct v; inv H; simpl in EVAL;
      try rewrite SF in *; simpl in EVAL; inv EVAL; eauto.
    rewrite H1. destruct (Int64.eq n Int64.zero) eqn:NULL.
    { eapply Val.cmplu_bool_inject with (v2:=Vlong n); eauto. simpl. rewrite SF, NULL. eauto. }
    { exploit cmplu_join_inj; try eapply H1; eauto. }
Qed.

Lemma eval_operation_join_inj op sp1 vl1 sp2 vl2 v1
    (PTRBINOP: ptr_binop op = true)
    (VINJ: Val.inject_list f vl1 vl2)
    (SPINJ: Val.inject f sp1 sp2)
    (EVAL: eval_operation_join ge1 sp1 op vl1 m1 = Some v1) :
  exists v2,
     <<EVAL': eval_operation_join ge2 sp2 op vl2 m2 = Some v2>>
   /\ <<VINJ': Val.inject f v1 v2>>.
Proof.
  unfold ptr_binop in PTRBINOP. destruct op; ss.
  (* psub *)
  - do 2 (destruct VINJ; [ss|]). destruct VINJ; [|ss]. dup H. dup H0.
    destruct Archi.ptr64 eqn:SF; simpl in *; ss.
    destruct v; destruct v0; inv H; inv H0; simpl in EVAL;
      try rewrite SF in *; simpl in EVAL; inv EVAL; eauto; try (by (des_ifs; esplits; eauto)); ss.
    { exploit Val.psubl_inject. eapply H1. eapply H2. i. esplits; eauto. }
    { exploit psubl_join_common_inj. eauto. eauto. eauto. eauto. eauto.
      eapply H1. eapply H2. eauto. i. des. subst. esplits; eauto. }
    { exploit psubl_join_common_inj. eauto. eauto. eauto. eauto. eauto.
      eapply H1. eapply H2. eauto. i. des. subst. esplits; eauto. }
    { exploit Val.psubl_inject. eapply H1. eapply H2. i. esplits; eauto. }
  - destruct (eval_condition_join cond vl1 m1) eqn:COND.
    2:{ ss. clarify. esplits; eauto. }
    exploit eval_condition_join_inj; eauto. i. rewrite H. inv EVAL. esplits; eauto.
    destruct b; ss; econs.
Qed.

Lemma eval_operation_wrapper_inj op sp1 vl1 sp2 vl2 v1
    (GLOB: forall id ofs,
           In id (globals_operation op) ->
           Val.inject f (Genv.symbol_address ge1 id ofs) (Genv.symbol_address ge2 id ofs))
    (VINJ: Val.inject_list f vl1 vl2)
    (SPINJ: Val.inject f sp1 sp2)
    (EVAL: eval_operation_wrapper ge1 sp1 op vl1 m1 = Some v1) :
  exists v2, <<EVAL': eval_operation_wrapper ge2 sp2 op vl2 m2 = Some v2>>
     /\ <<VINJ': Val.inject f v1 v2>>.
Proof.
  destruct (ptr_op op) eqn:PTROP; cycle 1.
  { rewrite eval_operation_no_ptr_op in *; eauto.
    eapply eval_operation_inj; eauto. }
  destruct (ptr_binop op) eqn:PTRBINOP; cycle 1.
  { unfold eval_operation_wrapper in *. destruct op; ss; clarify.
    destruct VINJ; ss. destruct VINJ; ss.
    destruct (eval_condition_join c vl m1) eqn:EVAL1; cycle 1.
    { clarify. esplits; eauto. }
    exploit eval_condition_join_inj; eauto. i. des.
    clarify. rewrite H1. ss. esplits; eauto.
    eapply Val.normalize_inject. des_ifs; ss. }
  unfold eval_operation_wrapper in *. rewrite PTROP in EVAL.
  assert (EVAL1: eval_operation_join ge1 sp1 op vl1 m1 = Some v1) by (destruct op; ss).
  exploit eval_operation_join_inj; try eapply EVAL1; eauto. i. des. rewrite EVAL'.
  destruct op; ss; esplits; eauto. des_ifs.
Qed.

Lemma eval_condition_wrapper_inj c vl1 vl2 b
    (VINJ: Val.inject_list f vl1 vl2)
    (EVAL: eval_condition_wrapper c vl1 m1 = Some b) :
  <<EVAL': eval_condition_wrapper c vl2 m2 = Some b>>.
Proof.
  destruct (ptr_cond c) eqn:COND.
  - unfold eval_condition_wrapper in *. des_ifs. eapply eval_condition_join_inj; eauto.
  - unfold eval_condition_wrapper in *. des_ifs. eapply eval_condition_inj; eauto.
Qed.

End EVAL_COMPAT.

Section EVAL_WRAPPER_LESSDEF.

Variable F V: Type.
Variable genv: Genv.t F V.
  
Lemma eval_condition_join_lessdef c vl1 vl2 m1 m2 b
    (PTRBINOP: ptr_cond c = true)
    (LESS: Val.lessdef_list vl1 vl2)
    (MEXT: Mem.extends m1 m2)
    (EVAL: eval_condition_join c vl1 m1 = Some b) :
  <<EVAL2: eval_condition_join c vl2 m2 = Some b>>.
Proof.
  assert (SAMEVLD: forall b ofs, Mem.valid_pointer m1 b ofs = true -> Mem.valid_pointer m2 b ofs = true).
  { ii. eapply Mem.valid_pointer_extends; eauto. }
  assert (SAMEWVLD: forall b ofs, Mem.weak_valid_pointer m1 b ofs = true -> Mem.weak_valid_pointer m2 b ofs = true).
  { ii. eapply Mem.weak_valid_pointer_extends; eauto. }
  unfold ptr_cond, ptr_uncond, ptr_bincond in PTRBINOP.
  destruct Archi.ptr64 eqn:SF; simpl in *; destruct c; simpl in PTRBINOP; inv PTRBINOP.
  (* cmplu *)
  - do 2 (destruct LESS; [ss|]). destruct LESS; [|ss].
    dup H. dup H0. unfold eval_condition_join, cmplu_join_common.
    destruct v1; destruct v0; inv H; inv H0; simpl in EVAL;
      try rewrite SF in *; simpl in EVAL; inv EVAL; eauto.
    + rewrite H0. destruct (Int64.eq i Int64.zero) eqn:NULL.
      { eapply Val.cmplu_bool_lessdef; eauto. simpl. rewrite SF, NULL. simpl. eauto. }
      { exploit cmplu_join_lessdef; try eapply H0; eauto. }
    + rewrite H0. destruct (Int64.eq i0 Int64.zero) eqn:NULL.
      { eapply Val.cmplu_bool_lessdef; eauto. simpl. rewrite SF, NULL. simpl. eauto. }
      { exploit cmplu_join_lessdef; try eapply H0; eauto. }
    + rewrite H0. eapply Val.cmplu_bool_lessdef; eauto.
  (* cmpluimm *)
  - destruct LESS; [ss|]. destruct LESS; [|ss].
    dup H. unfold eval_condition_join, cmplu_join_common.
    destruct v1; inv H; simpl in EVAL;
      try rewrite SF in *; simpl in EVAL; inv EVAL; eauto.
    rewrite H1. destruct (Int64.eq n Int64.zero) eqn:NULL.
    + eapply Val.cmplu_bool_lessdef with (v2:=Vlong n); eauto. simpl. rewrite SF, NULL. simpl. eauto.
    + exploit cmplu_join_lessdef; try eapply H1; eauto.
  (* cmpu *)
  - do 2 (destruct LESS; [ss|]). destruct LESS; [|ss].
    dup H. dup H0. unfold eval_condition_join, cmpu_join_common.
    destruct v1; destruct v0; inv H; inv H0; simpl in EVAL;
      try rewrite SF in *; simpl in EVAL; inv EVAL; eauto.
    + rewrite H0. destruct (Int.eq i Int.zero) eqn:NULL.
      { eapply Val.cmpu_bool_lessdef; eauto. simpl. rewrite SF, NULL. simpl. eauto. }
      { exploit cmpu_join_lessdef; try eapply H0; eauto. }
    + rewrite H0. destruct (Int.eq i0 Int.zero) eqn:NULL.
      { eapply Val.cmpu_bool_lessdef; eauto. simpl. rewrite SF, NULL. simpl. eauto. }
      { exploit cmpu_join_lessdef; try eapply H0; eauto. }
    + rewrite H0. eapply Val.cmpu_bool_lessdef; eauto. simpl. rewrite SF in *. eauto.
  (* cmpuimm *)
  - destruct LESS; [ss|]. destruct LESS; [|ss].
    dup H. unfold eval_condition_join, cmpu_join_common.
    destruct v1; inv H; simpl in EVAL;
      try rewrite SF in *; simpl in EVAL; inv EVAL; eauto.
    rewrite H1. destruct (Int.eq n Int.zero) eqn:NULL.
    + eapply Val.cmpu_bool_lessdef with (v2:=Vint n); eauto. simpl. rewrite SF, NULL. simpl. eauto.
    + exploit cmpu_join_lessdef; try eapply H1; eauto.
Qed.

Lemma eval_operation_join_lessdef
    sp op vl1 vl2 v1 m1 m2
    (PTRBINOP: ptr_binop op = true)
    (LESS: Val.lessdef_list vl1 vl2)
    (MEXT: Mem.extends m1 m2)
    (EVAL: eval_operation_join genv sp op vl1 m1 = Some v1) :
  exists v2, <<EVAL2: eval_operation_join genv sp op vl2 m2 = Some v2>> /\ <<LESS': Val.lessdef v1 v2>>.
Proof.
  unfold ptr_binop in PTRBINOP. destruct op; ss.
  (* psub *)
  - do 2 (destruct LESS; [ss|]). destruct LESS; [|ss]. dup H. dup H0.
    destruct Archi.ptr64 eqn:SF; simpl in *.
    (* psubl *)
    + destruct v0; destruct v3; inv H; inv H0; simpl in *;
        try rewrite SF in *; simpl in *; inv EVAL; eauto; clear SF; try (by (des_ifs; esplits; eauto)).
      { exploit psubl_join_lessdef. eapply H1. eapply H2. eapply MEXT. eauto. i. des.
        rewrite PSUB. esplits; eauto. }
      { exploit psubl_join_lessdef. eapply H1. eapply H2. eapply MEXT. eauto. i. des.
        rewrite PSUB. esplits; eauto. }
    (* psub *)
    + destruct v0; destruct v3; inv H; inv H0; simpl in *;
        try rewrite SF in *; simpl in *; inv EVAL; eauto; clear SF; try (by (des_ifs; esplits; eauto)).
      { exploit psub_join_lessdef. eapply H1. eapply H2. eapply MEXT. eauto. i. des.
        rewrite PSUB. esplits; eauto. }
      { exploit psub_join_lessdef. eapply H1. eapply H2. eapply MEXT. eauto. i. des.
        rewrite PSUB. esplits; eauto. }
  (* cmp *)
  - destruct (eval_condition_join cond vl1 m1) eqn:COND.
    2:{ ss. clarify. esplits; eauto. }
    exploit eval_condition_join_lessdef; eauto. i. rewrite H. inv EVAL. esplits; eauto.
Qed.

Lemma eval_operation_wrapper_lessdef
    sp op vl1 vl2 v1 m1 m2
    (LESS: Val.lessdef_list vl1 vl2)
    (MEXT: Mem.extends m1 m2)
    (EVAL: eval_operation_wrapper genv sp op vl1 m1 = Some v1) :
  exists v2, <<EVAL2: eval_operation_wrapper genv sp op vl2 m2 = Some v2>> /\ <<LESS': Val.lessdef v1 v2>>.
Proof.
  destruct (ptr_op op) eqn:PTROP; cycle 1.
  { unfold eval_operation_wrapper in *. rewrite PTROP in *.
    eapply eval_operation_lessdef; eauto. }
  destruct (ptr_binop op) eqn:PTRBINOP; cycle 1.
  { unfold eval_operation_wrapper in *. destruct op; ss; clarify.
    destruct LESS; ss. destruct LESS; ss.
    destruct (eval_condition_join c vl1 m1) eqn:EVAL1; cycle 1.
    { clarify. esplits; eauto. }
    exploit eval_condition_join_lessdef; eauto. i. des.
    clarify. rewrite H1. ss. esplits; eauto.
    eapply Val.normalize_lessdef. des_ifs; ss. }
  unfold eval_operation_wrapper in *. des_ifs_safe.
  assert (EVAL1: eval_operation_join genv sp op vl1 m1 = Some v1) by (destruct op; ss).
  exploit eval_operation_join_lessdef; eauto. i. des. rewrite EVAL2.
  destruct op; ss; esplits; eauto.
Qed.

Lemma eval_condition_wrapper_lessdef
    c vl1 vl2 b m1 m2
    (LESS: Val.lessdef_list vl1 vl2)
    (MEXT: Mem.extends m1 m2)
    (ECOND: eval_condition_wrapper c vl1 m1 = Some b) :
  <<ECOND': eval_condition_wrapper c vl2 m2 = Some b>>.
Proof.
  destruct (ptr_cond c) eqn:COND.
  - unfold eval_condition_wrapper in *. des_ifs. eapply eval_condition_join_lessdef; eauto.
  - unfold eval_condition_wrapper in *. des_ifs. eapply eval_condition_lessdef; eauto.
Qed.

End EVAL_WRAPPER_LESSDEF.

Section EVAL_WRAPPER_INJECT.

Variable F V: Type.
Variable genv: Genv.t F V.
Variable f: meminj.
Hypothesis globals: meminj_preserves_globals genv f.
Variable sp1: block.
Variable sp2: block.
Variable delta: Z.
Hypothesis sp_inj: f sp1 = Some(sp2, delta).

Lemma eval_condition_join_inject
    c vl1 vl2 m1 m2 b
    (PTRCOND: ptr_cond c = true)
    (VINJ: Val.inject_list f vl1 vl2)
    (MINJ: Mem.inject f m1 m2)
    (EVAL: eval_condition_join c vl1 m1 = Some b) :
  <<EVAL': eval_condition_join c vl2 m2 = Some b>>.
Proof.
  unfold ptr_cond, ptr_uncond, ptr_bincond in PTRCOND.
  destruct Archi.ptr64 eqn:SF; simpl in *; destruct c; simpl in PTRCOND; inv PTRCOND.
  (* cmplu *)
  - do 2 (destruct VINJ; [ss|]). destruct VINJ; [|ss]. dup H. dup H0. unfold eval_condition_join, cmplu_join_common.
    destruct v; destruct v0; inv H; inv H0; simpl in EVAL;
      try rewrite SF in *; simpl in EVAL; inv EVAL; eauto.
    + rewrite H0. destruct (Int64.eq i Int64.zero) eqn:NULL.
      { eapply cmplu_bool_inject'; eauto. simpl. rewrite SF, NULL. eauto. }
      { exploit cmplu_join_inject; try eapply H0; eauto. }
    + rewrite H0. destruct (Int64.eq i0 Int64.zero) eqn:NULL.
      { eapply cmplu_bool_inject'; eauto. simpl. rewrite SF, NULL. eauto. }
      { exploit cmplu_join_inject; try eapply H0; eauto. }
    + rewrite H0. eapply cmplu_bool_inject'; eauto.
  (* cmpluimm *)
  - destruct VINJ; [ss|]. destruct VINJ; [|ss]. dup H. unfold eval_condition_join, cmplu_join_common.
    destruct v; inv H; simpl in EVAL;
      try rewrite SF in *; simpl in EVAL; inv EVAL; eauto.
    rewrite H1. destruct (Int64.eq n Int64.zero) eqn:NULL.
    { eapply cmplu_bool_inject' with (v2:=Vlong n); eauto. simpl. rewrite SF, NULL. eauto. }
    { exploit cmplu_join_inject; try eapply H1; eauto. }
  (* cmpu *)
  - do 2 (destruct VINJ; [ss|]). destruct VINJ; [|ss]. dup H. dup H0. unfold eval_condition_join, cmpu_join_common.
    destruct v; destruct v0; inv H; inv H0; simpl in EVAL;
      try rewrite SF in *; simpl in EVAL; inv EVAL; eauto.
    + rewrite H0. destruct (Int.eq i Int.zero) eqn:NULL.
      { eapply cmpu_bool_inject'; eauto. simpl. rewrite SF, NULL. eauto. }
      { exploit cmpu_join_inject; try eapply H0; eauto. }
    + rewrite H0. destruct (Int.eq i0 Int.zero) eqn:NULL.
      { eapply cmpu_bool_inject'; eauto. simpl. rewrite SF, NULL. eauto. }
      { exploit cmpu_join_inject; try eapply H0; eauto. }
    + rewrite H0. eapply cmpu_bool_inject'; eauto. simpl. rewrite SF. eauto.
  (* cmpuimm *)
  - destruct VINJ; [ss|]. destruct VINJ; [|ss]. dup H. unfold eval_condition_join, cmpu_join_common.
    destruct v; inv H; simpl in EVAL;
      try rewrite SF in *; simpl in EVAL; inv EVAL; eauto.
    rewrite H1. destruct (Int.eq n Int.zero) eqn:NULL.
    { eapply cmpu_bool_inject' with (v2:=Vint n); eauto. simpl. rewrite SF, NULL. eauto. }
    { exploit cmpu_join_inject; try eapply H1; eauto. }
Qed.

Lemma eval_operation_join_inject
    op vl1 vl2 v1 m1 m2
    (PTRBINOP: ptr_binop op = true)
    (VINJ: Val.inject_list f vl1 vl2)
    (MINJ: Mem.inject f m1 m2)
    (EVAL: eval_operation_join genv (Vptr sp1 Ptrofs.zero) op vl1 m1 = Some v1) :
  exists v2, <<EVAL': eval_operation_join genv (Vptr sp2 Ptrofs.zero) (shift_stack_operation delta op) vl2 m2 = Some v2>>
   /\ <<VINJ': Val.inject f v1 v2>>.
Proof.
  unfold ptr_binop in PTRBINOP. destruct op; ss.
  (* psub *)
  - do 2 (destruct VINJ; [ss|]). destruct VINJ; [|ss]. dup H. dup H0.
    destruct Archi.ptr64 eqn:SF; simpl in *.
    (* psubl *)
    + destruct v; destruct v0; inv H; inv H0; simpl in EVAL;
        try rewrite SF in *; simpl in EVAL; inv EVAL; eauto; try (by (des_ifs; esplits; eauto)).
      { exploit Val.psubl_inject. eapply H1. eapply H2. i. esplits; eauto. }
      { exploit psubl_join_common_inject. eauto. eapply H1. eapply H2. eauto. eauto. i. des. subst. esplits; eauto. }
      { exploit psubl_join_common_inject. eauto. eapply H1. eapply H2. eauto. eauto. i. des. subst. esplits; eauto. }
      { exploit Val.psubl_inject. eapply H1. eapply H2. i. esplits; eauto. }
    (* psub *)
    + destruct v; destruct v0; inv H; inv H0; simpl in EVAL;
        try rewrite SF in *; simpl in EVAL; inv EVAL; eauto; try (by (des_ifs; esplits; eauto)).
  - destruct (eval_condition_join cond vl1 m1) eqn:COND.
    2:{ ss. clarify. esplits; eauto. }
    exploit eval_condition_join_inject; eauto. i. rewrite H. inv EVAL. esplits; eauto.
    destruct b; ss; econs.
Qed.

Lemma eval_operation_wrapper_inject
    op vl1 vl2 v1 m1 m2
    (VINJ: Val.inject_list f vl1 vl2)
    (MINJ: Mem.inject f m1 m2)
    (EVAL: eval_operation_wrapper genv (Vptr sp1 Ptrofs.zero) op vl1 m1 = Some v1) :
  exists v2, <<EVAL': eval_operation_wrapper genv (Vptr sp2 Ptrofs.zero) (shift_stack_operation delta op) vl2 m2 = Some v2>>
   /\ <<VINJ': Val.inject f v1 v2>>.
Proof.
  assert (SHIFT: ptr_op (shift_stack_operation delta op) = ptr_op op) by (destruct op; ss).
  assert (SHIFT': ptr_binop (shift_stack_operation delta op) = ptr_binop op) by (destruct op; ss).
  destruct (ptr_op op) eqn:PTROP; cycle 1.
  { unfold eval_operation_wrapper in *. rewrite SHIFT. rewrite PTROP in EVAL.
    eapply eval_operation_inject; eauto. }
  destruct (ptr_binop op) eqn:PTRBINOP; cycle 1.
  { unfold eval_operation_wrapper in *. destruct op; ss; clarify.
    destruct VINJ; ss. destruct VINJ; ss.
    destruct (eval_condition_join c vl m1) eqn:EVAL1; cycle 1.
    { clarify. esplits; eauto. }
    exploit eval_condition_join_inject; eauto. i. des.
    clarify. rewrite H1. ss. esplits; eauto.
    eapply Val.normalize_inject. des_ifs; ss. }
  unfold eval_operation_wrapper in *. rewrite PTROP in EVAL. rewrite SHIFT.
  assert (EVAL1: eval_operation_join genv (Vptr sp1 Ptrofs.zero) op vl1 m1 = Some v1) by (destruct op; ss).
  exploit eval_operation_join_inject; try eapply EVAL1; eauto. i. des. rewrite EVAL'.
  destruct op; ss; esplits; eauto.
Qed.

Lemma eval_condition_wrapper_inject
    c vl1 vl2 m1 m2 b
    (VINJ: Val.inject_list f vl1 vl2)
    (MINJ: Mem.inject f m1 m2)
    (EVAL: eval_condition_wrapper c vl1 m1 = Some b) :
  <<EVAL': eval_condition_wrapper c vl2 m2 = Some b>>.
Proof.
  destruct (ptr_cond c) eqn:COND.
  - unfold eval_condition_wrapper in *. des_ifs. eapply eval_condition_join_inject; eauto.
  - unfold eval_condition_wrapper in *. des_ifs. eapply eval_condition_inject; eauto.
Qed.

End EVAL_WRAPPER_INJECT.
