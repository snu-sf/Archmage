
(** Translation of RTL that normalizes the function code: it ensures
that only an [Inop] can lead to a junction point, that there are no two
successive join points, that the instruction at the join point is an
[Inop] and that the entry point of the function both (i) holds an
[Inop] instruction and (ii) does not have any predecessor.  *)

Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Kildall. 
Require Import Utils.
Require Import DLib.
Local Open Scope string_scope.
Unset Allow StrictProp.
(** * State monad used in the transformation *)

Record state: Type := mkstate {
  st_nextnode: positive;
  st_entry: positive;
  st_code: code
}.

Variant res (A: Type) (s: state): Type :=
  | Error: Errors.errmsg -> res A s
  | OK: A -> state -> res A s.
Arguments OK [A s].
Arguments Error [A s].

Definition mon (A: Type) : Type := forall (s: state), res A s.

Definition ret (A: Type) (x: A) : mon A :=
  fun (s: state) => OK x s.
 Arguments ret [A].

Definition bind (A B: Type) (f: mon A) (g: A -> mon B) : mon B :=
  fun (s: state) =>
    match f s with
    | Error msg => Error msg
    | OK a s' =>
        match g a s' with
        | Error msg => Error msg
        | OK b s''  => OK b s''
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

Fixpoint mfold {A B: Type} (f: A -> B -> mon B) (l: list A) (b: B) : mon B :=
  match l with
    | nil => ret b
    | hd :: tl =>
      do rhd <- f hd b;
      mfold f tl rhd
  end.

(** * Utility functions used in the transformation *)
  
(** Adding the [Inop] at the entry point [pc] of the function.  
   Returns the value of the new entrypoint of function. *)
Definition add_nop_entry (pc : node) : mon node :=
  fun s =>
    let pc_new := s.(st_nextnode) in
      OK pc_new
         (mkstate (Pos.succ pc_new) 
                  pc_new 
                  (PTree.set pc_new (Inop pc) s.(st_code)))
.

(** [add_nop pc'] adds a fresh [Inop pc'] to the graph.
    New instruction not reachable yet. *)
Definition add_nop (pc':node) : mon node :=
  fun s =>
    let pc_new := s.(st_nextnode) in
      if peq pc' s.(st_entry)
      then Error (Errors.msg "RTLnorm - 1")
      else OK pc_new
              (mkstate (Pos.succ pc_new) 
                       (st_entry s) 
                       (PTree.set pc_new (Inop pc') s.(st_code)))
.


(** Placing new [Inop] at junction points *)

(** Change all successors of [i] equal to [pc] for [pcnew]. 
    Leave others unchanged *)
Definition ch_successors (i:instruction) (pc pcnew: node) : instruction :=
  match i with 
    | Inop s => if (peq s pc) then Inop pcnew else i
    | Iop op1 args1 dst1 s => if (peq s pc) then Iop op1 args1 dst1 pcnew else i
    | Iload c1 a1 args1 dst1 s => if (peq s pc) then Iload c1 a1 args1 dst1 pcnew else i
    | Istore c1 a1 args1 dst1 s =>  if (peq s pc) then Istore c1 a1 args1 dst1 pcnew else i
    | Icall s1 id1 args1 dst1 s => if (peq s pc) then Icall s1 id1 args1 dst1 pcnew else i
    | Ibuiltin id1 args1 dst1 s => if (peq s pc) then Ibuiltin id1 args1 dst1 pcnew else i
    | Icond c1 args ifso ifnot => 
      if (peq ifso pc) then 
        if (peq ifnot pc) then Icond c1 args pcnew pcnew 
        else Icond c1 args pcnew ifnot
      else 
        if (peq ifnot pc) then Icond c1 args ifso pcnew
        else i
    | Ijumptable c1 succs1 => Ijumptable c1 (map (fun p => if (peq p pc) then pcnew else p) succs1)
    | Itailcall s1 id1 args1 => i
    | Ireturn r1 => i
  end. 

Definition upd_pred (preds_pc : list node) (pc pcnew: node) : mon unit :=
  mfold_unit (fun pred s => 
                match (st_code s) ! pred with 
                  | Some i => 
                    OK tt (mkstate (st_nextnode s)
                                   (st_entry s)
                                   (PTree.set pred (ch_successors i pc pcnew) (st_code s))) 
                  | None => Error (Errors.msg "RTLnorm - 2")
                end) 
             preds_pc.

Definition add_nop_at_jp (preds: node -> list node) (is_jp: node -> bool) (pcins: node * instruction) : mon unit := 
  let (pc,ins) := pcins in 
  if (is_jp pc) then 
    (do n <- add_nop pc ;
     do tt <- upd_pred (preds pc) pc n ;
     ret tt)
  else ret tt.

(** Placing fresh [Inop] at precessors of junction points *)
(** Updating to [a] the [k]th element of a list [l] *)
Fixpoint upd_nth {A: Type} (l: list A) (a: A) (k: nat) : (list A) :=
  match k with
    | O => match l with
             | nil => nil
             | x::m => a::m
           end
    | S p => match l with
               | nil => nil
               | x::m => x::(upd_nth m a p)
             end
  end.

(** Updating to [newsucc] the [k]th successors of instruction [ins] *)
Definition ins_newsucc (ins: instruction) (newsucc: node) (k : nat) : instruction :=
  match ins with
    | (Itailcall _ _ _)
    | (Ireturn _) => ins
    | (Icond cond args ifso ifnot) =>
      match k with
        | O  => Icond cond args newsucc ifnot
        | S O => Icond cond args ifso newsucc
        | _ => ins
      end
    | (Ijumptable arg tbl) => Ijumptable arg (upd_nth tbl newsucc k)
    | _ =>
      match k with
        | O =>
          match ins with
            | (Inop succ) => (Inop newsucc)
            | (Iop op args dst succ) => (Iop op args dst newsucc)
            | (Iload chunk addr args dst succ) => (Iload chunk addr args dst newsucc)
            | (Istore chunk addr args src succ) => (Istore chunk addr args src newsucc)
            | (Icall sig fn args dst succ) => (Icall sig fn args dst newsucc)
            | (Ibuiltin ef args dst succ) => (Ibuiltin ef args dst newsucc)
            | _ => ins
          end
        | _ => ins
      end
  end.
  
(** [upd_succ pc newsucc k] changes the [k]th successor of the
instruction at [pc] for the new sucessors given by [newsucc] *)
Definition upd_succ (pc: node) (newsucc:node) (k: nat): mon nat :=
  fun s =>
    match (st_code s) ! pc with
      | Some i => OK (S k)
                     (mkstate (st_nextnode s)
                              (st_entry s)
                              (PTree.set pc (ins_newsucc i newsucc k) s.(st_code)))
      | None => Error (Errors.msg "RTLnorm - 3")
    end.

(** [modif_ksucc] changes the instruction at [pc] concerning its
[k]th successor [succ]. It either does nothing, or add an [Inop] and
update the successors. *)
Definition modif_ksucc (is_jp:node->bool) (pc: node) (succ:node) (k: nat) : mon nat :=
    fun s => 
      match (st_code s) ! pc with
        | None 
        | Some (Ireturn _) 
        | Some (Itailcall _ _ _) => (Error (Errors.msg "RTLnorm - 4"))
        | _ =>
          if is_jp succ
            then
              (do n <- add_nop succ ;
               do k' <- upd_succ pc n k ;
                 ret k') s
              else ret (Datatypes.S k) s
        end.
  
(** [add_nop_after_instruction isjp (pc,ins)] adds a [Inop] after
    instruction [ins] that stands at node [pc]. *)
Definition add_nop_after_instruction (is_jp:node->bool) (pcins : node * instruction) : mon unit :=
  let (pc, ins) := pcins in
  do k <- mfold (modif_ksucc is_jp pc) (successors_instr ins) O ;
    ret tt.

(** * Initial state of the monad *)
Definition get_max {A: Type} (t: PTree.t A) : positive :=
  let elts := map (@fst positive A) (PTree.elements t) in
    fold_left (fun a pc => if plt a pc then pc else a) elts xH.

Definition init_state (f: RTL.function) : state :=
  mkstate (Pos.succ (get_max (fn_code f))) (fn_entrypoint f) (fn_code f).

Definition is_joinpoint (preds: PTree.t (list positive)) : node -> bool :=
  fun pc =>  match preds ! pc with
               | Some (x::y::m) => true
               | _ => false
             end.

(** * Checker *)
Lemma sum_eq_dec: forall {A B: Type},
                         (forall a1 a2:A, {a1 = a2} + {a1 <> a2}) ->
                         (forall b1 b2:B, {b1 = b2} + {b1 <> b2}) -> 
                  forall ab1 ab2: A+B , {ab1 = ab2} + {ab1 <> ab2}.
Proof.
    decide equality.
Defined.

Lemma builtin_arg_eq_dec : forall (A: Type),
    (forall a1 a2: A, { a1 = a2 } + { a1 <> a2 }) ->
    forall ba1 ba2: builtin_arg A, { ba1 = ba2 } + { ba1 <> ba2 }.
Proof.
  intros. 
  induction ba1; intros; go.
  - destruct ba2; try solve [right; discriminate].
    destruct (X x x0) ; go.
  - destruct ba2; try solve [right; discriminate].
    destruct (Int.eq_dec n n0); go.
  - destruct ba2; try solve [right; discriminate].
    destruct (Int64.eq_dec n n0); go.
  - destruct ba2; try solve [right; discriminate].
    destruct (Floats.Float.eq_dec f f0); go.
  - destruct ba2; try solve [right; discriminate].
    destruct (Floats.Float32.eq_dec f f0); go.
  - destruct ba2; try solve [right; discriminate].
    destruct (chunk_eq chunk chunk0);
      destruct (Ptrofs.eq_dec ofs ofs0); go.
  - destruct ba2; try solve [right; discriminate].
    destruct (Ptrofs.eq_dec ofs ofs0); go.
  - destruct ba2; try solve [right; discriminate].
    destruct (chunk_eq chunk chunk0);
      destruct (Ptrofs.eq_dec ofs ofs0);
      destruct (peq id id0) ; go.
  - destruct ba2; try solve [right; discriminate].
    destruct (Ptrofs.eq_dec ofs ofs0);
      destruct (peq id id0) ; go.
  - destruct ba2; try solve [right; discriminate].
    destruct (IHba1_1 ba2_1);
      destruct (IHba1_2 ba2_2);
      go.
  - destruct ba2; try solve [right; discriminate].
    destruct (IHba1_1 ba2_1);
      destruct (IHba1_2 ba2_2);
      go.
Defined.

Lemma builtin_res_eq_dec : forall (A: Type),
    (forall a1 a2: A, { a1 = a2 } + { a1 <> a2 }) ->
    forall br1 br2: builtin_res A, { br1 = br2 } + { br1 <> br2 }.
Proof.
  intros. 
  induction br1; intros; go.
  - destruct br2; try solve [right; discriminate].
    destruct (X x x0) ; go.
  - destruct br2; try solve [right; discriminate]; go.
  - destruct br2; try solve [right; discriminate].
     destruct (IHbr1_1 br2_1);
      destruct (IHbr1_2 br2_2);
      go.
Defined.

Definition ch_succ_dec (i1 i2: instruction) : bool :=
  match i1, i2 with 
    | Inop _ , Inop _ => 
      true
    | Iop op1 args1 dst1 _, Iop op2 args2 dst2 _ => 
      (eq_operation op1 op2)
        && (list_eq_dec peq args1 args2)
        && (peq dst1 dst2)
    | Iload c1 a1 args1 dst1 _, Iload c2 a2 args2 dst2 _  => 
      (chunk_eq c1 c2)
        && (eq_addressing a1 a2)
        && (list_eq_dec peq args1 args2)
        && (peq dst1 dst2)
    | Istore c1 a1 args1 dst1 _, Istore c2 a2 args2 dst2 _  => 
      (chunk_eq c1 c2) 
        && (eq_addressing a1 a2)
        && (list_eq_dec peq args1 args2)
        && (peq dst1 dst2)
    | Icall s1 id1 args1 dst1 _ , Icall s2 id2 args2 dst2 _ =>
      (signature_eq s1 s2) 
        && (sum_eq_dec peq peq id1 id2)
        && (list_eq_dec peq args1 args2)
        && (peq dst1 dst2)
    | Itailcall s1 id1 args1 , Itailcall s2 id2 args2 =>
      (signature_eq s1 s2)
        && (sum_eq_dec peq peq id1 id2)
        && (list_eq_dec peq args1 args2)
    | Ibuiltin id1 args1 dst1 _ , Ibuiltin id2 args2 dst2 _ =>
      (external_function_eq id1 id2)
        && (list_eq_dec (builtin_arg_eq_dec _ peq) args1 args2)
        && (builtin_res_eq_dec _ peq) dst1 dst2
    | Icond c1 args1 _ _ , Icond c2 args2 _ _ => 
      (eq_condition c1 c2)
        &&  (list_eq_dec peq args1 args2)
    | Ijumptable c1 succs1 , Ijumptable c2 succs2 => 
      (peq c1 c2)
        && (eq_nat_dec (length succs1) (length succs2))
    | Ireturn r1, Ireturn r2 =>
      (option_eq peq r1 r2)
    | _ , _ => false
  end
. 

(* There is a tunel of [Inop] of length length <= k in [tc] from [s2] to [s1] *)
Fixpoint inop_tunel (k:nat) (tc:code) (s1 s2:node)  : bool := 
  (peq s1 s2) 
    || 
    match k with 
      | O =>  false
      | S k => match tc ! s2 with 
                 | Some (Inop s3) => inop_tunel k tc s1 s3
                 | _ => false
               end
    end.

Definition check_mks_spec i ti tc : bool := 
  forall_list2 (inop_tunel 3 tc) (successors_instr i) (successors_instr ti).

Definition check_pc (c tc: code) (pc: node) (_:instruction) : bool :=
  match (c ! pc), (tc ! pc) with 
    | Some i, Some ti => ch_succ_dec i ti && check_mks_spec i ti tc
    | _,_ => false
  end.

Definition checker (c: code) (tc: code) : bool := 
  PTree.fold (fun res pc i => res && (check_pc c tc pc i)) c true. 

Definition check_entry (f tf: function) : bool := 
  match (fn_code tf) ! (fn_entrypoint tf) with
  | Some (Inop s) =>
    (peq s (fn_entrypoint f)) || inop_tunel 3 (fn_code tf) (fn_entrypoint f) s
  | _ => false
  end.

Definition transl_function (f: RTL.function) : Errors.res RTL.function :=
  match add_nop_entry (fn_entrypoint f) (init_state f) with
    | Error m => Errors.Error m
    | OK nentry s' =>
      let code_elts := PTree.elements s'.(st_code) in
      let preds := (make_predecessors (st_code s') successors_instr) in 
      let is_jp := is_joinpoint preds in
      match mfold_unit (add_nop_at_jp (fun p => preds !!! p) is_jp) code_elts s' with 
        | Error m => Errors.Error m 
        | OK u s'' => 
          let code_elts := PTree.elements s''.(st_code) in 
          let is_jp := is_joinpoint (make_predecessors (s''.(st_code)) successors_instr) in 
          match mfold_unit (add_nop_after_instruction is_jp) code_elts s'' with
            | Error m => Errors.Error m
            | OK u s'' => 
              let tf := (RTL.mkfunction
                           f.(RTL.fn_sig)
                           f.(RTL.fn_params)
                           f.(RTL.fn_stacksize)
                           s''.(st_code)
                           s''.(st_entry)) in 
              if checker (fn_code f) (fn_code tf) then
                if (check_entry f tf)
                then Errors.OK tf
                else Errors.Error (Errors.msg "RTLnorm - 5")
              else Errors.Error (Errors.msg "RTLnorm - 6")
          end
      end
  end.

Definition transl_fundef (f: RTL.fundef) : Errors.res RTL.fundef :=
  transf_partial_fundef transl_function f.

Definition transl_program (p: RTL.program) : Errors.res RTL.program :=
  transform_partial_program transl_fundef p.
