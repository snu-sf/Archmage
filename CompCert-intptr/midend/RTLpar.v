
(** The RTLpar intermediate language: abstract syntax and semantics. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import Floats.

Require Import Kildall.
Require Import Utils.
Require Import Relation_Operators.
Require Import Classical.
Require Import Relations.Relation_Definitions.
Require Import DLib.
Require Import SSA.
Require Import CSSA.
Require Parmov.
Require Import Dom.
Require Import Registers.
Require Import PointerOp.
Unset Allow StrictProp.

(** * Abstract syntax *)

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;

  fn_code: code;
  fn_parcopycode: parcopycode;

  fn_entrypoint: node
}.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Notation preds :=
  (fun f pc => (make_predecessors (fn_code f) successors_instr) !!! pc).

Inductive join_point (jp: node) (f:function) : Prop :=
  | jp_cons : forall l,
              forall (Hpreds: (make_predecessors (fn_code f) successors_instr) ! jp = Some l)
                     (Hl: (length l > 1)%nat),
                join_point jp f.

Definition successors (f: function) : PTree.t (list positive) :=
  PTree.map1 successors_instr (fn_code f).
Notation succs := (fun f pc => (successors f) !!! pc).

(** [cfg f i j] holds if [j] is a successor of [i] in the code of [f] *)
Variant cfg  (f : function) (i j:node) : Prop :=
| CFG : forall ins
               (HCFG_ins: (fn_code f) !i = Some ins)
               (HCFG_in : In j (successors_instr ins)),
    cfg f i j.
  
(** Well formed functions *)
Record wf_function (f:function) : Prop := {

  (* Code normalization *)
  fn_entry : exists s, (fn_code f) ! (fn_entrypoint f) = Some (Inop s);
  fn_entry_pred: forall pc, ~ cfg f pc (fn_entrypoint f);
  
  fn_normalized : forall jp pc, (* Only nop can lead to a jp *)
      join_point jp f ->
      In jp (succs f pc) -> (fn_code f) ! pc = Some (Inop jp);
  
  fn_normalized_jp : forall pc pc',  (* No two successive join points *)
      join_point pc' f ->
      cfg f pc pc' -> 
      ~ join_point pc f ;

  fn_parcb_jp: forall pc pc' parcb, (* Parcopy blocks before or at join_point *)
      (fn_code f) ! pc = Some (Inop pc') ->
      (fn_parcopycode f) ! pc = Some parcb ->
      ~ join_point pc' f ->
      join_point pc f;

  fn_parcb_inop: forall pc,
      (fn_parcopycode f) ! pc <> None ->
      exists s, (fn_code f) ! pc = Some (Inop s);

  (* Statements containment and reachability *)
  fn_code_closed: forall pc pc' instr, (fn_code f) ! pc = Some instr ->
                                       In pc' (successors_instr instr) ->
                                       exists instr', (fn_code f) ! pc' = Some instr'
}.

(** Well-formed function definitions *)
Variant wf_fundef: fundef -> Prop :=
  | wf_fundef_external: forall ef,
      wf_fundef (External ef)
  | wf_function_internal: forall f,
      wf_function f ->
      wf_fundef (Internal f).

(** Well-formed programs *)
Definition wf_program (p: program) : Prop :=
  forall f id, In (id, Gfun f) (prog_defs p) -> wf_fundef f.

(* Specification of [RTLparcleanup] phase : *)

Definition parcb_to_moves :=
  map (fun parc => match parc with  Iparcopy src dst => (src, dst) end).

Definition mill_function (f: function) : Prop := 
  forall pc parcb,
    (fn_parcopycode f) ! pc = Some parcb ->
    Parmov.is_mill _ (parcb_to_moves parcb).

Variant mill_fundef: fundef -> Prop :=
  | mill_fundef_external: forall ef,
      mill_fundef (External ef)
  | mill_function_internal: forall f,
      mill_function f ->
      mill_fundef (Internal f).

Definition mill_program (p: program) : Prop :=
  forall f id, In (id, Gfun f) (prog_defs p) -> mill_fundef f.

(** * Operational semantics *)

Definition genv := Genv.t fundef unit.

(** The same as CSSApar, but without phi-blocks *)
Variant stackframe : Type :=
  | Stackframe:
      forall (res: reg)        (**r where to store the result *)
             (f: function)     (**r calling function *)
             (sp: val)         (**r stack pointer in calling function *)
             (pc: node)        (**r program point in calling function *)
             (rs: regset),     (**r register state in calling function *)
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
| exec_Inop_njp:
    forall s f sp pc rs m pc',
    (fn_code f)!pc = Some(SSA.Inop pc') ->
    ~ join_point pc' f ->

    step (State s f sp pc rs m)
      E0 (State s f sp pc' rs m)
| exec_Inop_jp:
    forall s f sp pc rs m pc' parcb parcb',
    (fn_code f)!pc = Some(SSA.Inop pc') ->
    join_point pc' f -> 

    (fn_parcopycode f)!pc = Some parcb ->
    (fn_parcopycode f)!pc' = Some parcb' ->
    step (State s f sp pc rs m)
      E0 (State s f sp pc'
          (parcopy_store parcb'
              (parcopy_store parcb rs))
          m)
| exec_Iop:
    forall s f sp pc rs m op args res pc' v,
    (fn_code f)!pc = Some(SSA.Iop op args res pc') ->
    eval_operation_wrapper ge sp op rs## args m = Some v ->
    step (State s f sp pc rs m)
      E0 (State s f sp pc' (rs# res <- v) m)
| exec_Iload:
    forall s f sp pc rs m chunk addr args dst pc' a v,
    (fn_code f)!pc = Some(SSA.Iload chunk addr args dst pc') ->
    eval_addressing ge sp addr rs## args = Some a ->
    Mem.loadv chunk m a = Some v ->
    step (State s f sp pc rs m)
      E0 (State s f sp pc' (rs# dst <- v) m)
| exec_Istore:
    forall s f sp pc rs m chunk addr args src pc' a m',
    (fn_code f)!pc = Some(SSA.Istore chunk addr args src pc') ->
    eval_addressing ge sp addr rs## args = Some a ->
    Mem.storev chunk m a rs# src = Some m' ->
    step (State s f sp pc rs m)
      E0 (State s f sp pc' rs m')
| exec_Icall:
    forall s f sp pc rs m sig ros args res pc' fd,
    (fn_code f)!pc = Some(SSA.Icall sig ros args res pc') ->
    find_function (ros_to_vos m ros rs) rs = Some fd ->
    funsig fd = sig ->
    step (State s f sp pc rs m)
      E0 (Callstate (Stackframe res f sp pc' rs :: s) fd rs## args m)
| exec_Itailcall:
    forall s f stk pc rs m sig ros args fd m',
    (fn_code f)!pc = Some(SSA.Itailcall sig ros args) ->
    find_function (ros_to_vos m ros rs) rs = Some fd ->
    funsig fd = sig ->
    Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
    step (State s f (Vptr stk Ptrofs.zero) pc rs m)
         E0 (Callstate s fd rs## args m')
| exec_Ibuiltin:
  forall s f sp pc rs m ef args vargs res vres pc' t m',
    (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
    eval_builtin_args ge (fun r => rs# r) sp m args vargs ->
    external_call ef ge vargs m t vres m' ->
    step (State s f sp pc rs m)
    t (State s f sp pc' (regmap_setres res vres rs) m')
| exec_Icond_true:
    forall s f sp pc rs m cond args ifso ifnot,
    (fn_code f)!pc = Some(SSA.Icond cond args ifso ifnot) ->
    eval_condition_wrapper cond rs## args m = Some true ->
    step (State s f sp pc rs m)
      E0 (State s f sp ifso rs m)
| exec_Icond_false:
    forall s f sp pc rs m cond args ifso ifnot,
    (fn_code f)!pc = Some(SSA.Icond cond args ifso ifnot) ->
    eval_condition_wrapper cond rs## args m = Some false ->
    step (State s f sp pc rs m)
      E0 (State s f sp ifnot rs m)
| exec_Ijumptable:
    forall s f sp pc rs m arg tbl n pc',
    (fn_code f)!pc = Some(SSA.Ijumptable arg tbl) ->
    rs# arg = Vint n ->
    list_nth_z tbl (Int.unsigned n) = Some pc' ->
    step (State s f sp pc rs m)
      E0 (State s f sp pc' rs m)
| exec_Ireturn:
    forall s f stk pc rs m or m',
    (fn_code f)!pc = Some(SSA.Ireturn or) ->
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
      E0 (State s f sp pc (rs# res <- vres) m).

Hint Constructors step: core.

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
  | final_state_intro: forall r m, final_state (Returnstate nil (Vint r) m) r.

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
