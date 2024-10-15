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

(** The RTLt intermediate language: abstract syntax and semantics.

  Essentially a copy of RTL language, instrumented with a DFS list of
  program points in the CFG.
  
  Used in the middle-end to transfer useful properties : - any
  instruction in the function code is reachable from the entry point -
  the dfs list is both correct and complete

  Duplicating the file helps keeping non-intrusive wrt the rest of
  CompCert's chain.

*)

Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Registers.
Require Import RTL.
Require Import Relation_Operators Utils Dom.
Require Import PointerOp.
Unset Allow StrictProp.

(** * Abstract syntax *)

(** RTL is organized as instructions, functions and programs.
  Instructions correspond roughly to elementary instructions of the
  target processor, but take their arguments and leave their results
  in pseudo-registers (also called temporaries in textbooks).
  Infinitely many pseudo-registers are available, and each function
  has its own set of pseudo-registers, unaffected by function calls.

  Instructions are organized as a control-flow graph: a function is
  a finite map from ``nodes'' (abstract program points) to instructions,
  and each instruction lists explicitly the nodes of its successors.
*)

Definition code: Type := PTree.t RTL.instruction.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;
  fn_code: code;
  fn_entrypoint: node;
  fn_dfs: list node 
}.

(** A function description comprises a control-flow graph (CFG) [fn_code]
    (a partial finite mapping from nodes to instructions).  As in Cminor,
    [fn_sig] is the function signature and [fn_stacksize] the number of bytes
    for its stack-allocated activation record.  [fn_params] is the list
    of registers that are bound to the values of arguments at call time.
    [fn_entrypoint] is the node of the first instruction of the function
    in the CFG. *)

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

(** * Operational semantics *)

Definition genv := Genv.t fundef unit.
Definition regset := Regmap.t val.

Fixpoint init_regs (vl: list val) (rl: list reg) {struct rl} : regset :=
  match rl, vl with
  | r1 :: rs, v1 :: vs => Regmap.set r1 v1 (init_regs vs rs)
  | _, _ => Regmap.init Vundef
  end.

(** The dynamic semantics of RTL is given in small-step style, as a
  set of transitions between states.  A state captures the current
  point in the execution.  Three kinds of states appear in the transitions:

- [State cs f sp pc rs m] describes an execution point within a function.
  [f] is the current function.
  [sp] is the pointer to the stack block for its current activation
     (as in Cminor).
  [pc] is the current program point (CFG node) within the code [c].
  [rs] gives the current values for the pseudo-registers.
  [m] is the current memory state.
- [Callstate cs f args m] is an intermediate state that appears during
  function calls.
  [f] is the function definition that we are calling.
  [args] (a list of values) are the arguments for this call.
  [m] is the current memory state.
- [Returnstate cs v m] is an intermediate state that appears when a
  function terminates and returns to its caller.
  [v] is the return value and [m] the current memory state.

In all three kinds of states, the [cs] parameter represents the call stack.
It is a list of frames [Stackframe res f sp pc rs].  Each frame represents
a function call in progress.
[res] is the pseudo-register that will receive the result of the call.
[f] is the calling function.
[sp] is its stack pointer.
[pc] is the program point for the instruction that follows the call.
[rs] is the state of registers in the calling function.
*)

Variant stackframe : Type :=
  | Stackframe:
      forall (res: reg)            (**r where to store the result *)
             (f: function)         (**r calling function *)
             (sp: val)             (**r stack pointer in calling function *)
             (pc: node)            (**r program point in calling function *)
             (rs: regset),         (**r register state in calling function *)
      stackframe.

Variant state : Type :=
  | State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r current function *)
             (sp: val)                (**r stack pointer *)
             (pc: node)               (**r current program point in [c] *)
             (rs: regset)             (**r register state *)
             (m: mem),                (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (args: list val)         (**r arguments to the call *)
             (m: mem),                (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (v: val)                 (**r return value for the call *)
             (m: mem),                (**r memory state *)
      state.

Definition ros_to_vos (m: Mem.mem) (ros: reg + ident) (rs: regset) : val + ident :=
  match ros with
  | inl r => match rs#r with
            | Vint n => if negb Archi.ptr64
                       then (match Mem.to_ptr (Vint n) m with
                             | Some v' => inl v'
                             | None => inl rs#r
                             end)
                       else inl rs#r
            | Vlong n => if Archi.ptr64
                        then (match Mem.to_ptr (Vlong n) m with
                              | Some v' => inl v'
                              | None => inl rs#r
                              end)
                        else inl rs#r
            | _ => inl rs#r
            end
  | inr symb => inr symb
  end.

Section RELSEM.

Variable ge: genv.

Definition find_function
      (ros: val + ident) (rs: regset) : option fundef :=
  match ros with
  | inl r => Genv.find_funct ge r
  | inr symb =>
      match Genv.find_symbol ge symb with
      | None => None
      | Some b => Genv.find_funct_ptr ge b
      end
  end.

(** The transitions are presented as an inductive predicate
  [step ge st1 t st2], where [ge] is the global environment,
  [st1] the initial state, [st2] the final state, and [t] the trace
  of system calls performed during this transition. *)

Inductive step: state -> trace -> state -> Prop :=
  | exec_Inop:
      forall s f sp pc rs m pc',
      (fn_code f)!pc = Some(Inop pc') ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Iop:
      forall s f sp pc rs m op args res pc' v,
      (fn_code f)!pc = Some(Iop op args res pc') ->
      eval_operation_wrapper ge sp op rs##args m = Some v ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (rs#res <- v) m)
  | exec_Iload:
      forall s f sp pc rs m chunk addr args dst pc' a v,
      (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' (rs#dst <- v) m)
  | exec_Istore:
      forall s f sp pc rs m chunk addr args src pc' a m',
      (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m')
  | exec_Icall:
      forall s f sp pc rs m sig ros args res pc' fd,
      (fn_code f)!pc = Some(Icall sig ros args res pc') ->
      find_function (ros_to_vos m ros rs) rs = Some fd ->
      funsig fd = sig ->
      step (State s f sp pc rs m)
        E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs##args m)
  | exec_Itailcall:
      forall s f stk pc rs m sig ros args fd m',
      (fn_code f)!pc = Some(Itailcall sig ros args) ->
      find_function (ros_to_vos m ros rs) rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Ptrofs.zero) pc rs m)
        E0 (Callstate s fd rs##args m')
  | exec_Ibuiltin:
      forall s f sp pc rs m ef args res pc' vargs t vres m',
      (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
      eval_builtin_args ge (fun r => rs#r) sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State s f sp pc rs m)
         t (State s f sp pc' (regmap_setres res vres rs) m')
  | exec_Icond:
      forall s f sp pc rs m cond args ifso ifnot b pc',
      (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition_wrapper cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Ijumptable:
      forall s f sp pc rs m arg tbl n pc',
      (fn_code f)!pc = Some(Ijumptable arg tbl) ->
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      step (State s f sp pc rs m)
        E0 (State s f sp pc' rs m)
  | exec_Ireturn:
      forall s f stk pc rs m or m',
      (fn_code f)!pc = Some(Ireturn or) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s f (Vptr stk Ptrofs.zero) pc rs m)
        E0 (Returnstate s (regmap_optget or Vundef rs) m')
  | exec_function_internal:
      forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      step (Callstate s (Internal f) args m)
        E0 (State s
                  f
                  (Vptr stk Ptrofs.zero)
                  f.(fn_entrypoint)
                  (init_regs args f.(fn_params))
                  m')
  | exec_function_external:
      forall s ef args res t m m',
      external_call ef ge args m t res m' ->
      step (Callstate s (External ef) args m)
         t (Returnstate s res m')
  | exec_return:
      forall res f sp pc rs s vres m,
      step (Returnstate (Stackframe res f sp pc rs :: s) vres m)
        E0 (State s f sp pc (rs#res <- vres) m).

End RELSEM.

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty call stack. *)

Variant initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      initial_state p (Callstate nil f nil m0).

Inductive glob_capture (p: program) : state -> state -> Prop :=
  | glob_capture_intro
      f m pbs m'
      (* (INIT: initial_state p (Callstate nil f nil m)) *)
      (NONSTATIC: Genv.non_static_glob (Genv.globalenv p) (Genv.genv_public (Genv.globalenv p)) = pbs)
      (CAPTURE: Genv.capture_init_mem m pbs m') :
    glob_capture p (Callstate nil f nil m) (Callstate nil f nil m').

(** A final state is a [Returnstate] with an empty call stack. *)

Variant final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate nil (Vint r) m) r.

(** Non-deterministic external state *)

Definition is_external (ge:genv) (s:state) : Prop :=
  match s with
  | Callstate stk fd vargs m =>
    match fd with
    | External ef => is_external_ef ef
    | _ => False
    end
  | State cs f sp pc rs m =>
    match (fn_code f)!pc with
    | Some (Ibuiltin ef args res pc') => is_external_ef ef
    | _ => False
    end
  | _ => False
  end.

Definition state_mem (st: state) : mem :=
  match st with
  | State _ _ _ _ _ m => m
  | Callstate _ _ _ m => m
  | Returnstate _ _ m => m
  end.

Definition concrete_snapshot (ge: Senv.t) (st: state) (id: ident) : option Z :=
  if Senv.public_symbol ge id
  then (match Senv.find_symbol ge id with
        | Some b => Maps.PTree.get b (state_mem st).(Mem.mem_concrete)
        | None => None
        end
    )
  else None.

(** The small-step semantics for a program. *)

Definition semantics (p: program) :=
  Semantics step (initial_state p) (glob_capture p) (concrete_snapshot (Genv.globalenv p)) final_state is_external (Genv.globalenv p).

(** Computation of the possible successors of an instruction.
  This is used in particular for dataflow analyses. *)

Definition successors_instr (i: instruction) : list node :=
  match i with
  | Inop s => s :: nil
  | Iop op args res s => s :: nil
  | Iload chunk addr args dst s => s :: nil
  | Istore chunk addr args src s => s :: nil
  | Icall sig ros args res s => s :: nil
  | Itailcall sig ros args => nil
  | Ibuiltin ef args res s => s :: nil
  | Icond cond args ifso ifnot => ifso :: ifnot :: nil
  | Ijumptable arg tbl => tbl
  | Ireturn optarg => nil
  end.

Definition successors_map (f: function) : PTree.t (list node) :=
  PTree.map1 successors_instr f.(fn_code).


Variant rtl_cfg (f: function) (i j:node) : Prop :=
  | rtl_CFG : forall ins,
      forall (HCFG_ins: (fn_code f) !i = Some ins)
             (HCFG_in : In j (successors_instr ins)),
        rtl_cfg f i j.

