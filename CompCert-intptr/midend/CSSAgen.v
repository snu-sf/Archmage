(** translation from SSA to CSSApar form *)

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
Require Import CSSA.
Require Import Kildall.
Require Import Utils.
Require Import SSA.
Require Import SSAutils.
Require Import Bijection.

Unset Allow StrictProp.

Local Open Scope string_scope.

(** * Monad state for the transformation *)
Record state : Type := mkstate {
  next_fresh_reg: reg;    (** next fresh register for a new parallel copy *)
  st_phicode: phicode;            (** phicode being constructed *)
  st_parcopycode: CSSA.parcopycode     (** parcopycode being constructed *)
}.

Variant state_incr: state -> state -> Prop :=
  state_incr_intro:
    forall (s1 s2: state),
    (Ple (next_fresh_reg s1) (next_fresh_reg s2)) ->
    state_incr s1 s2.

Lemma state_incr_refl:
  forall s, state_incr s s.
Proof.
  intros; constructor.
  apply Ple_refl.
Qed.

Lemma state_incr_trans:
  forall s1 s2 s3,
  state_incr s1 s2 
  -> state_incr s2 s3 
  -> state_incr s1 s3.
Proof.
  intros; constructor; auto.
  eapply Ple_trans; inv H; inv H0; eauto.
Qed.

(** ** Monadic machinery *)
Variant res (A: Type) (s: state): Type :=
  | Error: Errors.errmsg -> res A s
  | OK: A -> forall (s': state), state_incr s s' -> res A s.

Arguments OK [A s].
Arguments Error [A s].

Definition mon (A : Type) := forall (s: state), res A s.

Definition ret (A: Type) (x: A) : mon A :=
  fun (s: state) => OK x s (state_incr_refl s).

Arguments ret [A].

Definition error (A: Type) (msg: Errors.errmsg) : mon A :=
  fun (s: state) => Error msg.

Arguments error [A].

Definition bind (A B: Type) (f: mon A) (g: A -> mon B) : mon B :=
  fun (s: state) =>
    match f s with
    | Error msg => Error msg
    | OK a s' i =>
        match g a s' with
        | Error msg => Error msg
        | OK b s'' i' => OK b s'' (state_incr_trans s s' s'' i i')
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

(** * The transformation *)

(** ** Building parallel copies from phi-instruction variables *)

(** next fresh register *)
Definition next_fs (fs : reg) :=
  (Pos.succ fs).

Remark gen_newreg_incr:
  forall s,
    state_incr s
      (mkstate
        (next_fs (next_fresh_reg s))
        (st_phicode s)
        (st_parcopycode s)).
Proof.
  intros; econstructor.
  simpl.
  apply Ple_succ.
Qed.

Definition gen_newreg (arg: reg) : mon reg :=
  fun s =>
    OK (next_fresh_reg s)
      (mkstate
        (next_fs (next_fresh_reg s))
        (st_phicode s)
        (st_parcopycode s))
      (gen_newreg_incr _).

Fixpoint gen_new_regs (args: list reg) : mon (list reg) :=
  match args with
  | nil => ret nil
  | arg :: args =>
      do newreg <- gen_newreg arg;
      do newregs <- gen_new_regs args;
      ret (newreg :: newregs)
  end.

(** ** Adding parallel copies *)
Remark add_parcopy_incr:
  forall s pc parcb,
    state_incr s
      (mkstate
        (next_fresh_reg s)
        (st_phicode s)
        (PTree.set pc parcb (st_parcopycode s))).
Proof.
  intros; constructor; auto.
  simpl.
  apply Ple_refl.
Qed.

Definition add_parcopy (parcopy: CSSA.parcopy) (pc: node) : mon unit :=
  fun s =>
    match PTree.get pc (st_parcopycode s) with
    | None => Error (Errors.msg "CSSAgen - 1")
    | Some parcopies =>
      let new_parcb := parcopy :: parcopies
      in
      OK tt
        (mkstate
          (next_fresh_reg s)
          (st_phicode s)
          (PTree.set pc new_parcb (st_parcopycode s)))
        (add_parcopy_incr _ _ _)
    end.

Fixpoint add_parcopies (parcopies: list CSSA.parcopy)
    (copy_nodes: list node) : mon unit :=
  match parcopies, copy_nodes with
  | parcopy :: parcopies, pc :: copy_nodes =>
      do u <- add_parcopies parcopies copy_nodes;
      add_parcopy parcopy pc
  | nil, nil => ret tt
  | _, _     => error (Errors.msg "add_parcopies")
  end.

(** ** Adding phi instruction with new variables *)
Remark add_new_phi_incr :
  forall s pc phib,
    state_incr s
      (mkstate
        (next_fresh_reg s)
        (PTree.set pc phib (st_phicode s))
        (st_parcopycode s)).
Proof.
  intros; constructor; auto.
  simpl. apply Ple_refl.
Qed.

Definition add_new_phi (dst': reg ) (args': list reg)
    (pc: node) :=
  fun s =>
  match PTree.get pc (st_phicode s) with
    | None => Error (Errors.msg "CSSAgen - 2")
    | Some phib' =>
        OK tt 
          (mkstate
            (next_fresh_reg s)
            (PTree.set pc (Iphi args' dst' :: phib')
              (st_phicode s))
            (st_parcopycode s))
          (add_new_phi_incr _ _ _)
  end.

Fixpoint build_parcopies (args args' : list reg) :=
  match args, args' with
  | nil, nil => ret nil
  | arg :: args, arg' :: args' =>
      do parcopies <- build_parcopies args args';
      ret (Iparcopy arg arg' :: parcopies)
  | _, _ => error (Errors.msg "build_parcopies")
  end.

Fixpoint handle_phi_block (preds: list node)
    (block: list phiinstruction) (pc: node)
    : mon unit :=
  match block with
  | nil => ret tt
  | Iphi args dst :: block =>
      do dst' <- gen_newreg dst;
      do args' <- gen_new_regs args;
      do u <- handle_phi_block preds block pc;
      do parcopies <- build_parcopies args args';
      do u' <- add_parcopy (Iparcopy dst' dst) pc;
      do u'' <- add_parcopies parcopies preds;
      add_new_phi dst' args' pc
  end.

Remark initialize_parcopy_block_incr :
  forall s pc,
  state_incr s
    (mkstate
      (next_fresh_reg s)
      (st_phicode s)
      (PTree.set pc nil (st_parcopycode s))).
Proof.
  intros; constructor.
  simpl. apply Ple_refl.
Qed.

Definition initialize_parcopy_block pc :=
  fun s =>
  OK tt
    (mkstate
      (next_fresh_reg s)
      (st_phicode s)
      (PTree.set pc nil (st_parcopycode s)))
    (initialize_parcopy_block_incr _ _).

Fixpoint initialize_parcopy_blocks nodes :=
  match nodes with
  | nil => ret tt
  | pc :: nodes =>
      do u <- initialize_parcopy_block pc;
      initialize_parcopy_blocks nodes
  end.

Remark initialize_phi_block_incr :
  forall s pc,
  state_incr s
    (mkstate
      (next_fresh_reg s)
      (PTree.set pc nil (st_phicode s))
      (st_parcopycode s)).
Proof.
  intros; constructor; simpl. apply Ple_refl.
Qed.

Definition initialize_phi_block pc :=
  fun s =>
  OK tt
    (mkstate
      (next_fresh_reg s)
      (PTree.set pc nil (st_phicode s))
      (st_parcopycode s))
    (initialize_phi_block_incr _ _).

Definition copy_node (predsfun: PTree.t (list node)) (code: code)
    (pcode: phicode) (pc: node) : mon unit :=
  match pcode ! pc with
  | None => ret tt
  | Some block =>
      match predsfun ! pc with
      | None => error (Errors.msg "copy_node")
      | Some preds => 
          do u <- initialize_phi_block pc;
          do u' <-
            initialize_parcopy_blocks (pc :: preds);
          handle_phi_block preds block pc
      end
  end.

(** ** functions to get a first fresh register  *)
Definition max_reg_in_list (l: list reg) :=
  List.fold_left (fun m r => Pos.max m r) l 1%positive.

Definition get_max_reg_in_ins (ins : SSA.instruction) :=
  match ins with
  | Inop _ => 1%positive
  | Iop _ args res _ => max_reg_in_list (res :: args)
  | Iload _ _ args dst _ => max_reg_in_list (dst :: args)
  | Istore _ _ args src _ => max_reg_in_list (src :: args)
  | Icall _ (inl r) args res _ => max_reg_in_list (r :: res :: args)
  | Icall _ _ args res _ => max_reg_in_list (res :: args)
  | Itailcall _ (inl r) args => max_reg_in_list (r :: args)
  | Itailcall _ _ args => max_reg_in_list args
  | Ibuiltin _ args res _ => max_reg_in_list ((params_of_builtin_res res) ++ (params_of_builtin_args args))
  | Icond _ args _ _ => max_reg_in_list args
  | Ijumptable arg _ => max_reg_in_list (arg :: nil)
  | Ireturn None => 1%positive
  | Ireturn (Some arg) => max_reg_in_list (arg :: nil)
  end.

Definition get_max_reg_in_phiins (phi: phiinstruction) :=
  match phi with
  | Iphi args res => max_reg_in_list (res :: args)
  end.

Definition get_max_reg_in_phib (phib: phiblock) :=
  List.fold_left
    (fun m phiins => Pos.max m (get_max_reg_in_phiins phiins))
    phib 1%positive.

Definition get_max_reg_in_phicode (pcode: phicode) :=
  PTree.fold (fun m pc phib => Pos.max m (get_max_reg_in_phib phib))
    pcode 1%positive.

Definition get_max_reg_in_code (code: code) :=
  PTree.fold (fun m pc ins => Pos.max m (get_max_reg_in_ins ins))
    code 1%positive.

Definition get_maxreg (f: SSA.function) := 
  Pos.max
    (get_max_reg_in_code (fn_code f))
    (Pos.max
      (get_max_reg_in_phicode (fn_phicode f))
      (max_reg_in_list (fn_params f))).

(** ** State initialisation *)
Definition init_state (f: SSA.function) :=
  (mkstate
    (Pos.succ (get_maxreg f))
    (PTree.empty phiblock)
    (PTree.empty CSSA.parcopyblock)
  , List.map fst (PTree.elements (fn_code f))).

(** ** Normalisation check *)

Definition check_node (f : SSA.function) (pc : node) :=
  match (fn_code f) ! pc with
  | Some (Inop succ) =>
      match (fn_phicode f) ! pc with
      | None => true
      | Some phib =>
          match (fn_phicode f) ! succ with
          | None => true
          | Some phib => false
          end
      end
  | _ => true
  end.

Definition check_joinpoints (f: SSA.function) :=
  forallb (check_node f)
    (map fst (PTree.elements (fn_code f))).

Definition check_inop_jp (f : SSA.function) (pc : node) :=
  match (fn_phicode f) ! pc with
  | Some phib =>
      match (fn_code f) ! pc with
      | Some (Inop succ) => true
      | _ => false
      end
  | None => true
  end.

Definition check_jp_inops (f: SSA.function) :=
  forallb (check_inop_jp f)
    (map fst (PTree.elements (fn_phicode f))).

Definition entry_point_not_jp_pred (entryp : node) (parcode : parcopycode) :=
  match parcode ! entryp with
  | Some parcb => false
  | None => true
  end.

(** ** Checks for well-formedness *)

(* check for NoDup in phi args and dst *)
Fixpoint check_nodup_in_reglist l visited :=
  match l with
  | nil => (true, visited)
  | r :: t =>
      if SSARegSet.mem r visited then (false, visited)
      else check_nodup_in_reglist t (SSARegSet.add r visited)
  end.

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

Definition check_phicode_for_dups_in_phib f :=
  forallb
    (fun pcphib =>
      match pcphib with
      | (pc, phib) =>
          check_nodup_in_phib phib SSARegSet.empty
      end)
    (PTree.elements (CSSA.fn_phicode f)).

Definition check_nb_args f preds :=
  forallb
    (fun pcphib =>
      match pcphib with
      | (pc, phib) =>
          forallb
            (fun phi =>
              match phi with
              | Iphi args dst =>
                  beq_nat (length preds !!! pc) (length args)
              end)
            phib
      end)
  (PTree.elements (CSSA.fn_phicode f)).

Definition check_parcbSome f preds :=
  forallb
    (fun pcphib =>
      match pcphib with
      | (pc, phib) =>
          forallb
            (fun pred =>
              match (CSSA.fn_parcopycode f) ! pred with
              | None => false
              | _ => true
              end)
            (preds !!! pc)
      end)
  (PTree.elements (CSSA.fn_phicode f)).

Definition check_parcb'Some f :=
  forallb
    (fun pcphib =>
      match pcphib with
      | (pc, phib) =>
            match (CSSA.fn_parcopycode f) ! pc with
            | None => false
            | _ => true
            end
      end)
  (PTree.elements (CSSA.fn_phicode f)).

Definition check_fn_parcb_inop f :=
  forallb
    (fun pcparcb =>
      match pcparcb with
      | (pc, parcb) =>
            match (CSSA.fn_code f) ! pc with
            | Some (Inop s) => true
            | _ => false
            end
      end)
  (PTree.elements (CSSA.fn_parcopycode f)).

Definition check_fn_parcbjp f :=
  forallb
    (fun pcparcb =>
      match pcparcb with
      | (pc, parcb) =>
          match (CSSA.fn_code f) ! pc with
          | Some (Inop pc') =>
              match (CSSA.fn_phicode f) ! pc' with
              | None =>
                  match (CSSA.fn_phicode f) ! pc with
                  | Some phib => true
                  | _ => false
                  end
              | _ => true
              end
          | _ => true
          end
      end)
    (PTree.elements (CSSA.fn_parcopycode f)).

Definition check_parcborparcb' f :=
  forallb
    (fun pcparcb =>
      match pcparcb with
      | (pc, parcb) =>
          match (CSSA.fn_code f) ! pc with
          | Some (Inop pc') =>
              match (CSSA.fn_phicode f) ! pc' with
              | None =>
                  match (CSSA.fn_phicode f) ! pc with
                  | Some phib => true
                  | _ => false
                  end
              | _ => true
              end
          | _ => false
          end
      end)
    (PTree.elements (CSSA.fn_parcopycode f)).

(** ** Global Translation *)
Definition transl_function (f: SSA.function) : Errors.res CSSA.function :=
  let '(init,lp) := init_state f in
  let predsfun := make_predecessors (fn_code f) successors_instr in
  match mfold_unit 
      (copy_node predsfun (fn_code f) (fn_phicode f))
      lp init with
  | Error m => Errors.Error m
  | OK u s H =>
      if check_joinpoints f
        && check_jp_inops f
        && entry_point_not_jp_pred f.(SSA.fn_entrypoint) s.(st_parcopycode)
      then
        let tf := (CSSA.mkfunction
            f.(SSA.fn_sig)
            f.(SSA.fn_params)
            f.(SSA.fn_stacksize)
            f.(SSA.fn_code)
            s.(st_phicode)
            s.(st_parcopycode)
            f.(SSA.fn_entrypoint))
        in
        if check_nb_args tf (get_preds tf) &&
           check_parcbSome tf (CSSA.get_preds tf) &&
           check_parcb'Some tf &&
           check_fn_parcb_inop tf &&
           check_fn_parcbjp tf &&
           check_parcborparcb' tf &&
           check_phicode_for_dups_in_phib tf
        then Errors.OK tf
        else Errors.Error (Errors.msg "checks")
      else
        Errors.Error (Errors.msg "check_joinpoints")
  end.

Definition transl_fundef (f: SSA.fundef) : Errors.res CSSA.fundef :=
  transf_partial_fundef transl_function f.

Definition transl_program (p: SSA.program) : Errors.res CSSA.program :=
  transform_partial_program transl_fundef p.
