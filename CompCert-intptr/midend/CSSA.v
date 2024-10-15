
(** The CSSA intermediate language: abstract syntax and semantics. *)

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
Require Import Dom.
Require Import PointerOp.

Unset Allow StrictProp.

(** * Abstract syntax *)

(** Instructions are those of SSA, plus parallel copy blocks. *)

(** [Iparcopy src dst] copies the value of [src] to [dst] *)
Variant parcopy: Type :=
| Iparcopy: reg -> reg -> parcopy.

(** parallel copy blocks are lists of parallel copy instructions *)
Definition parcopyblock := list parcopy.

Definition parcopycode: Type := PTree.t parcopyblock.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_params: list reg;
  fn_stacksize: Z;

  fn_code: code;
  fn_phicode: phicode;
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

Variant join_point (jp: node) (f:function) : Prop :=
| jp_cons : forall l,
    forall (Hpreds: (make_predecessors (fn_code f) successors_instr) ! jp = Some l)
           (Hl: (length l > 1)%nat),
      join_point jp f.

(** * Use and definition of registers *)
Section UDEF.

Variant assigned_parcopy_spec (parcopycode: parcopycode) (pc: node): reg -> Prop :=
| AIparcopy: forall parcb dst,
    (parcopycode ! pc) = Some parcb ->
    (exists src, List.In (Iparcopy src dst) parcb) ->
    assigned_parcopy_spec parcopycode pc dst.

Variable f : function.

(** [use_code r pc] holds whenever register [r] is used at [pc] in the regular code of [f] *)
Variant use_code : reg -> node -> Prop := 
| UIop: forall pc arg op args dst s,
  (fn_code f) !pc = Some (SSA.Iop op args dst s)  -> In arg args -> use_code arg pc
| UIload: forall pc arg chk adr args dst s,
  (fn_code f) !pc = Some (SSA.Iload chk adr args dst s) -> In arg args -> use_code arg pc
| UIcond: forall pc arg cond args s s',
  (fn_code f) !pc = Some (SSA.Icond cond args s s') -> In arg args -> use_code arg pc
| UIbuiltin: forall pc arg ef args dst s,
  (fn_code f) !pc = Some (SSA.Ibuiltin ef args dst s) -> In arg (params_of_builtin_args args) -> use_code arg pc
| UIstore: forall pc arg chk adr args src s,
  (fn_code f) !pc = Some (SSA.Istore chk adr args src s) -> In arg (src :: args) -> use_code arg pc
| UIcall: forall pc arg sig r args dst s,
  (fn_code f) !pc = Some (SSA.Icall sig (inl ident r) args dst s) -> In arg (r::args) -> use_code arg pc
| UItailcall: forall pc arg sig r args,
  (fn_code f) !pc = Some (SSA.Itailcall sig (inl ident r) args) -> In arg (r::args) -> use_code arg pc
| UIcall2: forall pc arg sig id args dst s,
  (fn_code f) !pc = Some (SSA.Icall sig (inr reg id) args dst s) -> In arg args -> use_code arg pc
| UItailcall2: forall pc arg sig id args,
  (fn_code f) !pc = Some (SSA.Itailcall sig (inr reg id) args) -> In arg args -> use_code arg pc
| UIjump: forall pc arg tbl,
  (fn_code f) !pc = Some (SSA.Ijumptable arg tbl) -> use_code arg pc
| UIret: forall pc arg,
  (fn_code f) !pc = Some (SSA.Ireturn (Some arg)) -> use_code arg pc.

(** [use_phicode r pc] holds whenever register [r] is used at [pc] in the phi-code of [f] *)
Variant use_phicode : reg -> node -> Prop :=
| upc_intro : forall pc pred k arg args dst phib
  (PHIB: (fn_phicode f) ! pc = Some phib)
  (ASSIG : In (SSA.Iphi args dst) phib)
  (KARG : nth_error args k = Some arg)
  (KPRED : index_pred (make_predecessors (fn_code f) successors_instr) pred pc = Some k),
  use_phicode arg pred.

(** [use_parcopycode r pc] holds whenever register [r] is used at [pc] in
    parallel copy code of [f] *)
Variant use_parcopycode : reg -> node -> Prop :=
| uparc_intro : forall pc parcb src dst
    (PARCB: (fn_parcopycode f) ! pc = Some parcb)
    (ASSIG: In (Iparcopy src dst) parcb),
    use_parcopycode src pc.

(** A register is used in the code, or in the phicode, or in the parcopycode of
    a function *)
Variant use : reg -> node -> Prop :=
| u_code : forall x pc, use_code x pc -> use x pc
| u_phicode : forall x pc, use_phicode x pc -> use x pc
| u_parcopycode : forall x pc, use_parcopycode x pc -> use x pc.

(** Special definition point for function parameters and registers that are
    used in the function without having been defined anywhere in the function *)
Inductive ext_params (x: reg) : Prop :=
| ext_params_params :
  In x (fn_params f) -> ext_params x
| ext_params_undef :
  (exists pc, use x pc) ->
  (forall pc, ~ assigned_phi_spec (fn_phicode f) pc x) ->
  (forall pc, ~ assigned_code_spec (fn_code f) pc x) ->
  (forall pc, ~ assigned_parcopy_spec (fn_parcopycode f) pc x) ->
  ext_params x.

Hint Constructors ext_params: core.

(** [def r pc] holds if register [r] is defined at node [pc] *)
Inductive def : reg -> node -> Prop :=
| def_params : forall x,
    ext_params x -> def x (fn_entrypoint f)
| def_code : forall x pc, assigned_code_spec (fn_code f) pc x -> def x pc
| def_phicode : forall x pc, assigned_phi_spec (fn_phicode f) pc x -> def x pc
| def_parcopycode : forall x pc,
    assigned_parcopy_spec (fn_parcopycode f) pc x -> def x pc.


End UDEF.

Global Hint Constructors ext_params def assigned_code_spec assigned_phi_spec: core.

(** * Formalization of Dominators *)
Section DOMINATORS.

  Variable f : function.

  Definition entry := (fn_entrypoint f).
  Notation code := (fn_code f).

  (** [cfg i j] holds if [j] is a successor of [i] in the code of [f] *)
  Variant _cfg (i j:node) : Prop :=
  | CFG : forall ins
    (HCFG_ins: code !i = Some ins)
    (HCFG_in : In j (successors_instr ins)),
      _cfg i j.

  Definition exit (pc: node) : Prop :=
  match code ! pc with
  | Some (SSA.Itailcall _ _ _)
  | Some (SSA.Ireturn _) => True
  | Some (SSA.Ijumptable _ succs) => succs = nil
  | _ => False
  end.

  Definition cfg := _cfg.

  Definition dom := dom cfg exit entry.

End DOMINATORS.

(** * Well-formed CSSA functions *)

(** Every variable is assigned at most once *)
Definition unique_def_spec (f : function) :=
  (forall (r:reg) (pc pc':node),
    (assigned_code_spec (f.(fn_code)) pc r ->
      assigned_code_spec (f.(fn_code)) pc' r ->
      pc = pc')
    /\
    (assigned_phi_spec (f.(fn_phicode)) pc r ->
      assigned_phi_spec (f.(fn_phicode)) pc' r ->
      pc = pc')
    /\
    (assigned_parcopy_spec (f.(fn_parcopycode)) pc r ->
      assigned_parcopy_spec (f.(fn_parcopycode)) pc' r ->
      pc = pc')
    /\
    (
      (assigned_code_spec (f.(fn_code)) pc r ->
        ~ assigned_phi_spec (f.(fn_phicode)) pc' r)
      /\
      (assigned_code_spec (f.(fn_code)) pc r ->
        ~ assigned_parcopy_spec (f.(fn_parcopycode)) pc' r)
      /\
      (assigned_phi_spec (f.(fn_phicode)) pc r ->
        ~ assigned_code_spec (f.(fn_code)) pc' r)
      /\
      (assigned_phi_spec (f.(fn_phicode)) pc r ->
        ~ assigned_parcopy_spec (f.(fn_parcopycode)) pc' r)
      /\
      (assigned_parcopy_spec (f.(fn_parcopycode)) pc r ->
        ~ assigned_code_spec (f.(fn_code)) pc' r)
      /\
      (assigned_parcopy_spec (f.(fn_parcopycode)) pc r ->
        ~ assigned_phi_spec (f.(fn_phicode)) pc' r)
    )
  )
  /\
  (forall pc phiinstr,
    (f.(fn_phicode))!pc = Some phiinstr ->
    ( (NoDup phiinstr)
      /\ (forall r args args',
          In (SSA.Iphi args r) phiinstr -> In (SSA.Iphi args' r) phiinstr -> args = args'))
  )
  /\
  (forall pc parcb,
    (fn_parcopycode f) ! pc = Some parcb ->
    NoDup parcb /\ (forall dst src src',
      In (Iparcopy src dst) parcb -> In (Iparcopy src' dst) parcb -> src = src')).

(** All phi-instruction have the right numbers of phi-arguments *)
Definition block_nb_args (f: function) : Prop :=
  forall pc block args  x,
    (fn_phicode f) ! pc = Some block ->
    In (SSA.Iphi args x) block ->
    (length (preds f pc)) = (length args).

Definition successors (f: function) : PTree.t (list positive) :=
  PTree.map1 successors_instr (fn_code f).

Notation succs := (fun f pc => (successors f) !!! pc).

(** Liveness *)

Notation reached := (fun f => (reached (cfg f) (entry f))).
Notation sdom := (fun f => (sdom (cfg f) (exit f) (entry f))).

(* def of r strict dom pc *)
Variant cssadom (f : function) (r : reg) (pc : node) : Prop :=
| cssadom_sdom: forall def_r,
    def f r def_r ->
    sdom f def_r pc ->
    cssadom f r pc
| cssadom_phi:
    assigned_phi_spec (fn_phicode f) pc r ->
    cssadom f r pc
| cssadom_parcb':
    assigned_parcopy_spec (fn_parcopycode f) pc r ->
    join_point pc f ->
    cssadom f r pc.

(* Live in *)
Inductive cssalive_spec (f : function) (r : reg)
   (pc : node) : Prop :=
| cssalive_spec_use :
    ~ def f r pc ->
    use f r pc ->
    cssalive_spec f r pc
| cssalive_spec_pred :
    forall pc',
    cfg f pc pc' ->
    ~ def f r pc ->
    cssalive_spec f r pc' ->
    cssalive_spec f r pc
| cssalive_spec_entry :
    forall pc',
    cfg f pc pc' ->
    pc = fn_entrypoint f ->
    cssalive_spec f r pc' ->
    cssalive_spec f r pc.
(*
  Avec ces choix :
  u_k vivant en pred
  u_0 vivant en pc
  
  Du coup les u_i ont tous des live range
  totalement disjoints.

  Si on arrête la SSA-valeur aux phi-instrutions, on ne
  peut pas fusionner deux classes d'équivalence.

  Par contre, on peut quand même éliminer des copies pour
  chaque source a_k qui n'interfère avec aucune des
  variables de la classe de la destination de la copie.

  La question importante: si deux variables ont des
  live-range disjoints pour cette notion de liveness,
  peuvent-elles vraiment être fusionnées.

  => Il s'agit bien d'une sur-approximation.
*)

Inductive cssaliveout_spec (f : function) (r : reg)
   (pc : node) : Prop :=
| cssaliveout_spec_use :
    forall pc',
    cfg f pc pc' ->
    ~ def f r pc' ->
    use f r pc' ->
    cssaliveout_spec f r pc
| cssaliveout_spec_trans :
    forall pc',
    cfg f pc pc' ->
    ~ def f r pc' ->
    cssaliveout_spec f r pc' ->
    cssaliveout_spec f r pc.
(* NOTE: avec ce cssaliveout, les phi-ressources d'une même phi-instruction ont
   bien des live-range disjoints, vu qu'elles sont à chaque fois utilisées
   et définies au même point, et n'apparaissent ailleurs *)

(* non interference for liveness:
     def(r1) not in live(r2) (and symmetrically) and def(r1) <> def(r2) *)

Inductive ninterlive_spec (f : function) (r1 r2 : reg) 
  : Prop :=
| ninterlive_spec_intro:
    forall d1 d2,
    def f r1 d1 ->
    def f r2 d2 ->
    ~ cssaliveout_spec f r1 d2 ->
    ~ cssaliveout_spec f r2 d1 ->
    d1 <> d2 -> (* trop technique, et insuffisant si pas les autres invariants structurels *)
    ninterlive_spec f r1 r2.

Definition get_preds f :=
  make_predecessors (fn_code f) successors_instr.

(** Well-formed CSSA functions *)

Record wf_cssa_function (f:function) : Prop := {

(* Semantics well defined, including normalization *)
  fn_wf_block: block_nb_args f;

  fn_entry : exists s, (fn_code f) ! (fn_entrypoint f) = Some (Inop s);
  fn_entry_pred: forall pc, ~ cfg f pc (fn_entrypoint f);
  fn_no_parcb_at_entry : (fn_parcopycode f) ! (fn_entrypoint f) = None;

  fn_phicode_inv: forall jp,
                    join_point jp f <->
                    f.(fn_phicode) ! jp <> None;


  fn_normalized: forall jp pc,
                   (join_point jp f) ->
                   In jp (succs f pc) -> (fn_code f) ! pc = Some (Inop jp);

  fn_inop_in_jp : forall pc,
                    (fn_phicode f) ! pc <> None ->
                    exists succ, (fn_code f) ! pc = Some (Inop succ);

  fn_normalized_jp : forall pc preds,
                       (fn_phicode f) ! pc <> None ->
                       (get_preds f) ! pc = Some preds ->
                       forall pred, In pred preds -> (fn_phicode f) ! pred = None;

  parcbSome: forall phib pc
                     (phibSome: (fn_phicode f) ! pc = Some phib),
             forall pred, In pred (get_preds f) !!! pc -> 
                          (fn_parcopycode f) ! pred <> None;
  
  parcb'Some: forall phib pc
                     (phibSome: (fn_phicode f) ! pc = Some phib),
                (fn_parcopycode f) ! pc <> None;

  fn_parcbjp: forall pc pc' parcb,
            (fn_parcopycode f) ! pc = Some parcb ->
            (fn_code f) ! pc = Some (Inop pc') ->
            ~ join_point pc' f ->
            join_point pc f;

  parcb_inop: forall pc,
            (fn_parcopycode f) ! pc <> None ->
            exists s, (fn_code f) ! pc = Some (Inop s);

(* Statements containment and reachability *)
  fn_code_reached: forall pc ins, (fn_code f) ! pc = Some ins -> reached f pc;

  fn_code_closed: forall pc pc' instr, (fn_code f) ! pc = Some instr ->
                                       In pc' (successors_instr instr) ->
                                       exists instr', (fn_code f) ! pc' = Some instr';

(* Unique def *)                                                
  fn_cssa : unique_def_spec f;

  fn_cssa_params : forall x, In x (fn_params f) ->
    (forall pc, ~ assigned_code_spec (fn_code f) pc x) /\
    (forall pc, ~ assigned_phi_spec (fn_phicode f) pc x) /\
    (forall pc, ~ assigned_parcopy_spec (fn_parcopycode f) pc x);

(* Strict dominance *)
  fn_strict : forall x u d, use f x u -> def f x d -> dom f d u;

  fn_use_def_code : forall x pc,
    use_code f x pc ->
    assigned_code_spec (fn_code f) pc x -> False;

  fn_strict_use_parcb :
    forall x pc,
    use_parcopycode f x pc ->
    ~ assigned_parcopy_spec (fn_parcopycode f) pc x;

(* NOTE: Ces contraintes plus rigides sont pratiques,
     permettent un calcul de liveness optimisé, et simplifient le calcul
     d'interférences pour des raisons de liveness *)
  fn_jp_use_parcb' :
    forall x pc,
    join_point pc f ->
    use_parcopycode f x pc ->
    assigned_phi_spec (fn_phicode f) pc x;

  fn_jp_use_phib :
    forall x pc,
    use_phicode f x pc ->
    assigned_parcopy_spec (fn_parcopycode f) pc x
}.
  
(** Well-formed CSSA function definitions *)
Inductive wf_cssa_fundef: fundef -> Prop :=
  | wf_cssa_fundef_external: forall ef,
      wf_cssa_fundef (External ef)
  | wf_cssa_function_internal: forall f,
      wf_cssa_function f ->
      wf_cssa_fundef (Internal f).

(** Well-formed CSSA programs *)
Definition wf_cssa_program (p: program) : Prop :=
  forall f id, In (id, Gfun f) (prog_defs p) -> wf_cssa_fundef f.

(** * Operational semantics *)

Definition genv := Genv.t fundef unit.

(** The same as SSA, but with parallel copies at junction points and their
    predecessors *)
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

Fixpoint parcopy_store parcb (rs: regset) :=
  match parcb with
  | nil => rs
  | (Iparcopy src dst) :: parcb =>
      (parcopy_store parcb rs)# dst <- (rs # src)
  end.

(** The transitions are presented as an inductive predicate
  [step ge st1 t st2], where [ge] is the global environment,
  [st1] the initial state, [st2] the final state, and [t] the trace
  of system calls performed during this transition. *)

Inductive step: state -> trace -> state -> Prop :=
| exec_Inop_njp:
    forall s f sp pc rs m pc',
    (fn_code f) ! pc = Some (SSA.Inop pc') ->
    ~ join_point pc' f ->
    step (State s f sp pc rs m)
      E0 (State s f sp pc' rs m)
| exec_Inop_jp:
    forall s f sp pc rs m pc' phib k parcb parcb',
    (fn_code f) ! pc = Some (SSA.Inop pc') ->
    join_point pc' f ->
    (fn_phicode f) ! pc' = Some phib ->
    (fn_parcopycode f) ! pc = Some parcb ->
    (fn_parcopycode f) ! pc' = Some parcb' ->
    index_pred (get_preds f) pc pc' = Some k ->
    step (State s f sp pc rs m)
      E0 (State s f sp pc'
          (parcopy_store parcb'
            (phi_store k phib
              (parcopy_store parcb rs)))
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
    (fn_code f)!pc = Some(SSA.Ibuiltin ef args res pc') ->
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

(** The small-step semantics for a program. *)
Definition semantics (p: program) :=
  Semantics step (initial_state p) (glob_capture p) (concrete_snapshot (Genv.globalenv p)) final_state is_external (Genv.globalenv p).

Definition parc_dst (pcopy : parcopy) :=
  match pcopy with
  | Iparcopy src dst => dst
  end.

Definition parc_src (pcopy : parcopy) :=
  match pcopy with
  | Iparcopy src dst => src
  end.

Notation CSSApath := (fun f => Dom.path (cfg f) (exit f) (entry f)).

Lemma correspondance_outin :
  forall f r pc',
  wf_cssa_function f ->
  cssalive_spec f r pc' ->
  forall pc,
  cfg f pc pc' ->
  cssaliveout_spec f r pc.
Proof.
  intros f r pc' WF H.
  induction H; intros; go.
  rewrite H0 in *.
  assert(~ cfg f pc0 (fn_entrypoint f)).
  induction WF; go.
  congruence.
Qed.

