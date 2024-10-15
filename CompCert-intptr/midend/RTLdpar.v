(** Destruction of RTLpar *)
Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Switch.
Require Import Op.
Require Import Registers.
Require Import CminorSel.
Require Import RTL.
Require Import Kildall. 
Require Import Utils.
Require Import SSAutils.
Require Import Bijection.
Require Import DLib.
Require Import CSSA.
Require CSSAgen.
Require Import RTLpar.

Unset Allow StrictProp.

Local Open Scope string_scope.

(** ** Some utility functions *)
Definition get_max_reg_in_parc (parc : parcopy) :=
  match parc with
  | Iparcopy src dst => CSSAgen.max_reg_in_list (src :: dst :: nil)
  end.

Definition get_max_reg_in_parcb (parcb : parcopyblock) :=
  List.fold_left
    (fun m parc => Pos.max m (get_max_reg_in_parc parc))
    parcb 1%positive.

Definition get_max_reg_in_parcode (parcode : parcopycode) :=
  PTree.fold1
    (fun m parcb => Pos.max m (get_max_reg_in_parcb parcb))
    parcode 1%positive.

Definition get_maxreg (f : function) :=
  Pos.max
    (CSSAgen.get_max_reg_in_code (fn_code f))
    (Pos.max
      (get_max_reg_in_parcode (fn_parcopycode f))
      (CSSAgen.max_reg_in_list (fn_params f))).

Definition fresh_init (f : function) : reg :=
  (Pos.succ (get_maxreg f)).

(** * Monad state for the transformation *)
Record state : Type := mkstate {
  st_nextnode_cp:   node;        (** next point to copy *)
  st_first_fs:      node;        (** the least fresh node where to add a move, constant *)
  st_nextnode_fs:   node;        (** the next node where to add *)
  st_code:          RTL.code;
  st_renum:         PTree.t node; (** renumbering of program points *)
  st_wf_next:       Plt st_nextnode_cp st_first_fs ; (** copied nodes and fresh nodes are diff *)
  st_wf_next_fs :   Ple st_first_fs st_nextnode_fs ; (** first fresh comes before the next fresh *)
  st_wf: forall (pc: node), 
    Plt pc st_nextnode_cp                            (** node already copied *)
    \/ (Plt pc st_nextnode_fs /\ Ple st_first_fs pc) (** a move node has already been added *)
    \/ (st_code!pc = None)                           (** no instruction yet *)
}.

Variant state_incr: state -> state -> Prop :=
| state_incr_intro : forall (s1 s2: state),
  Ple (st_nextnode_cp s1) (st_nextnode_cp s2) ->
  Ple (st_nextnode_fs s1) (st_nextnode_fs s2) ->
  (st_first_fs s1 = st_first_fs s2) ->
  (forall pc, s1.(st_code)!pc = None \/ s1.(st_code)!pc = s2.(st_code)!pc) ->
  state_incr s1 s2.

Lemma state_incr_refl:
  forall s, state_incr s s.
Proof.
  intros. 
  econstructor ; eauto. 
  apply Ple_refl.
  apply Ple_refl.
Qed.

Lemma state_incr_trans:
  forall s1 s2 s3, state_incr s1 s2 -> state_incr s2 s3 -> state_incr s1 s3.
Proof.
  intros. inv H; inv H0 ; intuition.
  econstructor ; eauto.
  - apply Ple_trans with (st_nextnode_cp s2); assumption.
  - apply Ple_trans with (st_nextnode_fs s2); assumption.  
  - congruence.
  - intros.
    generalize (H4 pc) (H7 pc). 
    intros; repeat invh or; try congruence; auto.
    + left ; congruence.
    + right ; congruence.
Qed.

(** ** Additional Monadic machinery *)
Variant res (A: Type) (s: state): Type :=
  | Error: Errors.errmsg -> res A s
  | OK: A -> forall (s': state), state_incr s s' -> res A s.

Arguments OK [A s].
Arguments Error [A s].

Definition mon (A: Type) : Type := forall (s: state), res A s.

Definition ret (A: Type) (x: A) : mon A :=
  fun (s: state) => OK x s (state_incr_refl s).

Arguments ret [A].

Definition bind (A B: Type) (f: mon A) (g: A -> mon B) : mon B :=
  fun (s: state) =>
    match f s with
    | Error msg => Error msg
    | OK a s' i =>
        match g a s' with
        | Error msg => Error msg
        | OK b s'' i'  => OK b s'' (state_incr_trans s s' s'' i i')
        end
    end.

Arguments bind [A B].

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200).

Fixpoint mfold_unit {A: Type} (f: A -> mon unit) (l: list A) : mon unit :=
  match l with
    | nil => ret tt
    | hd :: tl => (do rhd <- f hd ; mfold_unit f tl)
  end.

(** * Transformation *)

(** ** Getting the code boundaries *)
Definition get_max {A: Type} (t: PTree.t A) : (positive * list positive) :=
  let elts := map (@fst positive A) (PTree.elements t) in
    fold_left (fun (al: positive * list positive) pc => 
      let (a,l) := al in if plt a pc then (pc,pc::l) else (a,pc::l)) elts (xH,nil).

Definition get_min {A: Type} (t: PTree.t A) (max: positive) : positive :=
  let elts := map (@fst positive A) (PTree.elements t) in
    fold_left (fun acc pc => if plt pc acc then pc else acc) elts max.

Lemma get_max_fold_aux' : forall l e maxacc lacc, 
  In e l \/ In e lacc ->
  In e (snd (fold_left (fun (al: positive * list positive) pc => 
    let (a,l) := al in 
    if plt a pc then (pc, pc::l) else (a, pc::l)) l (maxacc,lacc))).
Proof.
  induction l ; intros; inv H; try inv H0; simpl; auto;
    [ destruct (plt maxacc e) ;  eapply IHl ; eauto
      | destruct (plt maxacc a) ;  eapply IHl ; eauto
      | destruct (plt maxacc a) ;  eapply IHl ; eauto]. 
Qed.   

Lemma get_max_in : forall (A: Type) t pc (a:A), 
  t ! pc = Some a -> In pc (snd (get_max t)).
Proof.
  unfold get_max ; intros.
  exploit PTree.elements_correct ; eauto. intros.
  assert (Hinpc : In (fst (pc,a)) (map (@fst positive A) (PTree.elements t))) by (eapply in_map ; eauto).
  simpl in Hinpc. 
  eapply (get_max_fold_aux'); eauto.
Qed.  

Ltac sz := unfold Plt, Ple in * ; zify ; lia.

Notation plus_2 :=  (fun p => (Pos.succ (Pos.succ p))). 

Lemma get_min_fold_aux : forall l minacc,
  Ple (fold_left (fun a pc => if plt pc a then pc else a) l minacc) minacc.
Proof.
  induction l ; intros.
  simpl. apply Ple_refl.
  simpl.
  destruct (plt a minacc).
  assert (Ha := IHl a).
  eapply Plt_Ple in p.
  eapply (Ple_trans (fold_left (fun a pc => if plt pc a then pc else a) l a) a minacc ); eauto.
  eapply IHl ; eauto.
Qed.

Lemma min_max : forall {A:Type} code, 
  Ple (@get_min A code (fst (get_max code))) (fst (get_max code)).
Proof.
  intros. generalize get_min_fold_aux; intros.
  unfold get_min. eauto.
Qed.

(** ** Initial state of the monad *)
Lemma init_state_wf_next : forall (f: RTLpar.function),
  Plt (get_min (fn_code f) (fst (get_max (RTLpar.fn_code f)))) 
      (plus_2 (fst (get_max (RTLpar.fn_code f)))).
Proof.
intros.
generalize (min_max (fn_code f)) ; intros ; sz ; lia.
Qed.

Lemma init_state_wf :
  forall f,
    let max := fst (get_max (fn_code f)) in
      forall  pc,
        Plt pc (get_min (fn_code f) max)
        \/ (Plt pc (plus_2 max)) /\ (Ple (plus_2 max) pc)
    \/ (PTree.empty RTL.instruction) ! pc = None .
Proof.
  intros.
  right ; right.
  apply PTree.gempty.
Qed.

Definition init_state (f: RTLpar.function) : (state * positive * list positive) :=
  let maxlp := (get_max (fn_code f)) in 
    ((mkstate 
      (get_min (fn_code f) (fst maxlp))
      (plus_2 (fst maxlp))
      (plus_2 (fst maxlp))
      (PTree.empty RTL.instruction)
      (PTree.empty node)
      (init_state_wf_next _ )
      (Ple_refl (plus_2 (fst maxlp)))
      (init_state_wf f)) , 
     fst maxlp, 
     snd maxlp).

(** ** Auxiliary functions *)

(** [next code pc diff] gets the next copy point in code [code]
starting from [pc]. Should terminate after [diff] steps of recursion
*)
Fixpoint next (code : SSA.code) (pc:node) (diff: nat)  : node := 
  match code ! pc with 
    | Some _ => pc
    | None => 
      match diff with 
        | O => pc (* corner case when pc = max *)
        | S k => next code (Pos.succ pc) k
      end
  end.
  
Lemma next_lt : forall code  diff pc,
  Plt pc (next code (Pos.succ pc) diff).
Proof.
  induction diff ; intros.
  simpl. destruct (code ! (Pos.succ pc)) ; apply Plt_succ.  
  simpl. destruct (code ! (Pos.succ pc)).
  apply Plt_succ.
  assert (HH:= IHdiff (Pos.succ pc)).
  exploit (Plt_trans pc (Pos.succ pc)) ; eauto.
  eapply Plt_succ; eauto. 
Qed.  

(** [copy_ins pc max ins code] copies the instruction [ins] at program
point [pc] that should be in the code [code]. *)
  
Lemma copy_ins_wf : forall s i code diff pc ,
  Plt pc (next code (Pos.succ (st_nextnode_cp s)) diff)  
  \/ (Plt pc (st_nextnode_fs s) /\ Ple (st_first_fs s) pc)
  \/ (PTree.set (st_nextnode_cp s) i (st_code s)) ! pc = None    
.
Proof.
  intros.
  destruct (peq pc (st_nextnode_cp s)).
  - subst. left. apply next_lt ; auto.
  - destruct (st_wf s pc).
    + left.
      generalize (next_lt code diff (st_nextnode_cp s)) ; intros.
      eapply Plt_trans in H0; eauto. 
    + repeat invh or ; repeat invh and; auto.
      right. right. rewrite PTree.gso ; auto.
Qed.

Lemma copy_ins_incr : forall code diff  s ins
  (H : Plt (next code (Pos.succ (st_nextnode_cp s)) diff) (st_first_fs s)),
  state_incr s
  (mkstate
    (next code (Pos.succ (st_nextnode_cp s)) diff)
    (st_first_fs s)
    (st_nextnode_fs s)
    (PTree.set (st_nextnode_cp s) ins (st_code s))
    (PTree.set (st_nextnode_cp s) (st_nextnode_cp s) (st_renum s))
    H
    (st_wf_next_fs s)
    (copy_ins_wf s ins code diff)).
Proof.
  intros.
  econstructor ; eauto ; simpl.
  - apply Plt_Ple. apply next_lt.
  - apply Ple_refl.
  - intros.
    destruct (st_wf s pc) ; simpl in *.
    + rewrite PTree.gso ; auto ; sz.
    + repeat invh or; repeat invh and; auto.
      rewrite PTree.gso ; auto.
      generalize (next_lt code diff (st_nextnode_cp s)) ; intros.
      sz.
Qed.

Definition copy_ins (pc max: node) (ins: RTL.instruction) (code: SSA.code) : mon unit := 
  fun s => 
    let nx_cp := st_nextnode_cp s in 
      let nxt := (next code (Pos.succ nx_cp) (((nat_of_P max) - (S (nat_of_P pc)))%nat)) in
        match plt nxt (st_first_fs s) with 
          | left H =>
            match peq pc nx_cp with 
              | left H' =>
                OK tt 
                (mkstate 
                  nxt
                  (st_first_fs s)
                  (st_nextnode_fs s)
                  (PTree.set nx_cp ins (st_code s))
                  (PTree.set nx_cp nx_cp (st_renum s))
                  H
                  (st_wf_next_fs s)
                  (copy_ins_wf s ins _ _ ))
                (copy_ins_incr _ _ _ _ H)
              | right _ => Error (Errors.msg (pos_to_string pc)) 
            end
          | right _ => Error (Errors.msg (pos_to_string pc))
        end.


(** [incr_next_cp] just goes to the next program point to copy *)
Lemma incr_next_cp_wf : forall s (H : Plt (Pos.succ (st_nextnode_cp s)) (st_first_fs s)), 
  forall pc : node,
             Plt pc (Pos.succ (st_nextnode_cp s)) \/
             Plt pc (st_nextnode_fs s) /\ Ple (st_first_fs s) pc \/
                                          (st_code s) ! pc = None.
Proof.
  intros.
  destruct (st_wf s pc).
  left ; sz.
  intuition.
Qed. 

Lemma incr_next_cp_incr : forall s H, 
  state_incr s (mkstate 
    (Pos.succ (st_nextnode_cp s))
    (st_first_fs s)
    (st_nextnode_fs s)
    (st_code s)
    (st_renum s)
    H
    (st_wf_next_fs s) 
    (incr_next_cp_wf s H)).
Proof.
  intros.
  constructor ; auto; simpl in *; sz.
Qed.

(** Replacing parallel copies with seq copies *)

Require Parmov.

Definition seq_parmoves (fresh : reg) : list (reg * reg) -> list (reg * reg) :=
  Parmov.parmove reg peq (fun _ => fresh).

(* [copy_move s pc (src,dst)] puts at [pc] an [Omove src dst fresh] while de-indexing *)
Lemma add_move_wf: forall s dst src  succ (pc: node),
  Plt pc (st_nextnode_cp s) \/
  Plt pc (Pos.succ (st_nextnode_fs s)) /\ Ple (st_first_fs s) pc \/
  (PTree.set (st_nextnode_fs s)
     (Iop Omove (src :: nil) dst succ) (st_code s)) ! pc = None.
Proof.
  intros.
  destruct (peq pc (st_nextnode_fs s)). 
  - inv e. right ; left. 
    split. 
    + apply Plt_succ ; auto.
    + apply (st_wf_next_fs s).
  - destruct (st_wf s pc) as [Hcase1 | [ [Hcase21 Hcase22] | Hcase3]].  
    + left ; auto.
    + right ; left. intuition.
      (* apply Ple_Plt_succ ; eauto. *)
      (* apply Plt_Ple ; auto. *)
    + right ; right.
      rewrite PTree.gso ; auto.  
Qed.

Lemma add_move_incr : forall s src dst succ,
state_incr s
           (mkstate 
              (st_nextnode_cp s)
              (st_first_fs s)
              (Pos.succ (st_nextnode_fs s))
              (PTree.set (st_nextnode_fs s)
                         (Iop Omove (src :: nil) dst succ) 
                         (st_code s))
              (st_renum s)
              (st_wf_next s)
              (Ple_trans (st_first_fs s) (st_nextnode_fs s)
                         (Pos.succ (st_nextnode_fs s)) (st_wf_next_fs s) 
                         (Ple_succ (st_nextnode_fs s)))
              (add_move_wf s dst src succ)). 
Proof.
  intros.
  econstructor ; eauto ; simpl in *.
  - apply Ple_refl.
  - apply Ple_succ.
  - intros.
    destruct (st_wf s pc) ; simpl in *.
    + generalize (st_wf_next_fs s) ; intros.
      generalize (st_wf_next s) ; intros.
      right. rewrite PTree.gso; auto. intro Hcont. inv Hcont. sz.
    + repeat invh or ; repeat invh and ; auto with coqlib. 
      right. rewrite PTree.gso ; auto with coqlib.
Qed.
  
Definition add_move (mov : reg * reg) : mon unit :=
  fun s =>
    match mov with
    | (src, dst) =>
          let nx_fs := st_nextnode_fs s in 
          OK tt
             (mkstate
                (st_nextnode_cp s)
                (st_first_fs s)
                (Pos.succ nx_fs)
                (PTree.set nx_fs (RTL.Iop Omove (src :: nil) dst
                                          (Pos.succ nx_fs))
                           (st_code s))
                (st_renum s)
                (st_wf_next s)
                (Ple_trans _ _ _ (st_wf_next_fs s) (Ple_succ nx_fs))
                (add_move_wf s dst src (Pos.succ nx_fs))
             )
             (add_move_incr _ _ _ _)
    end.
        
(** Adding a [Inop] *)
Lemma add_nop_pc_wf : forall s pc' pc,
             Plt pc (st_nextnode_cp s) \/
             Plt pc (Pos.succ (st_nextnode_fs s)) /\ Ple (st_first_fs s) pc \/
             (PTree.set (st_nextnode_fs s) (RTL.Inop pc') (st_code s)) ! pc = None.
Proof.
  intros.  
  destruct (peq pc (st_nextnode_fs s)). 
  - inv e. right ; left. 
    split. 
    + apply Plt_succ ; auto.
    + generalize (st_wf_next_fs s) (st_wf_next s) ; intros; auto.
  - destruct (st_wf s pc).
    + left. auto. 
    + repeat invh or ; repeat invh and.
      * right ; left.
        split ; auto. 
        eapply Plt_trans ; eauto. eapply Plt_succ.
      * right. right. rewrite PTree.gso ; auto. 
Qed.        

Lemma add_nop_pc_incr : forall opc s pc, 
  state_incr s (mkstate 
      (st_nextnode_cp s)
      (st_first_fs s)
      (Pos.succ (st_nextnode_fs s))
      (PTree.set (st_nextnode_fs s) (RTL.Inop pc) (st_code s))
      (match opc with 
             | Some pc => (PTree.set  pc (st_nextnode_fs s) (st_renum s))
             | None => (st_renum s)
           end)
      (st_wf_next s)
      (Ple_trans _ _ _ (st_wf_next_fs s) (Ple_succ (st_nextnode_fs s)) )
      (add_nop_pc_wf s pc)).
Proof.
  intros.
  econstructor ; eauto ; simpl in *.
  apply Ple_refl.
  apply Ple_succ.
  
  intros.
  destruct (st_wf s (st_nextnode_fs s)).
  generalize (st_wf_next_fs s) (st_wf_next s); intros.
  apply False_ind. sz.

  repeat invh or ; repeat invh and; auto.
  generalize (st_wf_next_fs s) (st_wf_next s); intros.
  apply False_ind. sz.
  
  destruct (peq pc0 (st_nextnode_fs s)).
  inv e. auto.
  rewrite PTree.gso ; auto ; sz.
Qed.
  
Definition add_nop_pc (from: option node) (pc: node) : mon unit := 
  fun s =>
    OK tt 
       (mkstate 
          (st_nextnode_cp s)
          (st_first_fs s)
          (Pos.succ (st_nextnode_fs s))
          (PTree.set (st_nextnode_fs s) (RTL.Inop pc) (st_code s))
          (match from with 
             | Some pc => (PTree.set  pc (st_nextnode_fs s) (st_renum s))
             | None => (st_renum s)
           end)
          (st_wf_next s)
          (Ple_trans _ _ _ (st_wf_next_fs s) (Ple_succ (st_nextnode_fs s)))
          (add_nop_pc_wf s pc))
       (add_nop_pc_incr _ _ _).

Fixpoint add_moves (Rfrom: option node) (last : node) (parcb : list (reg * reg)) : mon unit :=
    match parcb with
      | nil => add_nop_pc Rfrom last        
      | parc :: parcb =>
        do u <- add_move parc;
          add_moves Rfrom last parcb 
    end.

(** From SSA to RTL instructions *)
Definition map_pamr  (ins : SSA.instruction) : RTL.instruction :=
  match ins with 
    | SSA.Inop s =>  RTL.Inop s
    | SSA.Iop op args dst s => RTL.Iop op args dst s
    | SSA.Iload ch ad args dst s => RTL.Iload ch ad args dst s
    | SSA.Istore ch ad args src s => RTL.Istore ch ad args src s
    | SSA.Icall sig ros args dst s => RTL.Icall sig ros args dst s
    | SSA.Itailcall sig ros args => RTL.Itailcall sig ros args
    | SSA.Ibuiltin ef args dst s => RTL.Ibuiltin ef args dst s
    | SSA.Icond cond args ifso ifnot => RTL.Icond cond args ifso ifnot
    | SSA.Ijumptable arg tbl => RTL.Ijumptable arg tbl
    | SSA.Ireturn rop => RTL.Ireturn rop
  end.

(** ** Copying the code of the function, whilst performing unindexing and inlining
       of copy blocks  *)
Definition copy_inop (pc max: node) (code:SSA.code) : mon unit :=
  fun s => copy_ins pc max (RTL.Inop (st_nextnode_fs s)) code s.

Definition copy_wwo_add (tmp_reg: reg)  (preds: PTree.t (list node)) (code : SSA.code) 
                        (pcode : CSSA.parcopycode) (max pc: node) : mon unit :=
  fun s =>
    match code ! pc with 
      | None => 
        match plt (Pos.succ (st_nextnode_cp s)) (st_first_fs s) with 
          | left H =>
            OK tt (mkstate 
                     (Pos.succ (st_nextnode_cp s))
                     (st_first_fs s)
                     (st_nextnode_fs s)
                     (st_code s)
                     (st_renum s)
                     H
                     (st_wf_next_fs s) 
                     (incr_next_cp_wf s H))
               (incr_next_cp_incr s H)
          | right _ => Error (Errors.msg "copy_wwo_add : error in copy") 
        end
      | Some (SSA.Inop succ) => 
         match preds !!! succ with 
           | nil => Error (Errors.msg "copy_wwo_add : inconsistent preds")
           | _::nil => 
             (* succ is no junction point. 
                1. copy instruction (pc: Inop fresh)
                2. pc can be a join point : add potential par moves
                   at pc (and branch at [last] to succ !)
                3. set R(pc) to last fresh nop
              *)
             match pcode ! pc with 
               | None =>  copy_ins pc max (RTL.Inop succ) code s
               | Some parcb => 
                 let mvs := parcb_to_moves parcb in 
                   (do u <-copy_inop pc max code ;
                    do u'<-add_moves (Some pc) succ (seq_parmoves tmp_reg mvs); 
                    ret tt) s
             end
           | preds =>  
             (* succ is a join point (and pc is not). 
               1. copy instruction (pc: Inop fresh)
               2. insert par moves at pc (and branch last move to succ !)
               3. leave R(pc) to pc (already set in copy_inop)
             *)
             match pcode ! pc with
               | None => Error (Errors.msg "copy_wwo_add : no pcode")
               | Some parcb =>
                 let mvs := parcb_to_moves parcb in 
                 (do u <- copy_inop pc max code ; 
                  do n <- add_moves None succ (seq_parmoves tmp_reg mvs);
                 ret tt) s
             end
         end
      | Some ins => (* no junction point -> just convert to RTL type *)
        copy_ins pc max (map_pamr ins) code s
    end.

(** ** Sorting a list *)
Lemma Ple_total : forall p1 p2, Ple p1 p2 \/ Ple p2 p1.
Proof.
  intros.
  unfold Ple. zify ; lia.
Qed.

Lemma Ple_dec : forall p1 p2, {Ple p1 p2} + {~ Ple p1 p2}.
Proof.
  intros.
  unfold Ple in *.
  generalize (zle (Zpos p1) (Zpos p2)) ; eauto; intros.
  case H; intros ; eauto.
Defined.

Require Import List Setoid Permutation Sorted Orders.

Module PosOrder <: TotalLeBool.
  Definition t := positive.
  Definition leb (x y: t) := 
    match Ple_dec x y with 
      | left _ => true
      | right _ => false
    end.
  Infix "<=?" := leb (at level 70).
  Theorem leb_total : forall a1 a2, a1 <=? a2 = true \/ a2 <=? a1 = true.
    Proof. 
      intros.
      unfold leb.
      destruct (Ple_total a1 a2); (destruct (Ple_dec); intuition).
      right. destruct (Ple_dec); intuition.
    Qed.
End PosOrder.

Require Import Sorting.
Module Import PosSort := Mergesort.Sort PosOrder.

Definition sort_pp (l : list node) := sort l.

Definition transl_function (f: RTLpar.function) : Errors.res RTL.function :=
  let '(init,max,lp) := init_state f in 
  let fresh := fresh_init f in
  let preds := make_predecessors (RTLpar.fn_code f) SSA.successors_instr in
  match mfold_unit (copy_wwo_add fresh preds 
                                 (fn_code f) (fn_parcopycode f) max) (sort_pp lp) init with
    | Error m => Errors.Error m
    | OK u s'' H => 
      Errors.OK (RTL.mkfunction (RTLpar.fn_sig f)
                                (RTLpar.fn_params f)
                                (RTLpar.fn_stacksize f)
                                (st_code s'')
                                (RTLpar.fn_entrypoint f)) 
  end.

Definition transl_fundef := transf_partial_fundef transl_function.

Definition transl_program (p: RTLpar.program) : Errors.res RTL.program :=
  transform_partial_program transl_fundef p.
