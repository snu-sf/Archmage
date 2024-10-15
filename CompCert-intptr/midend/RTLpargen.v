(** Coalescing and RTLpar generation *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Dom.
Require Import Op.
Require Import SSA.
Require Import SSAutils.
Require Import Utils.
Require Import CSSA.
Require RTLpar.
Require Import Kildall.
Require Import KildallComp.
Require Import DLib.
Require Import CSSAutils.
Require CSSAlive.
Require Import Registers.

Section TRANSFORMATION.

Notation "a @@ f" := (f a)
    (at level 50, left associativity).

(** ** compute variables definition point *)

Definition defined_var ins :=
  match ins with
  | Iop _ _ r _      => Some r
  | Iload _ _ _ r _  => Some r
  | Icall _ _ _ r _  => Some r
  | Ibuiltin _ _ (BR r) _ => Some r
  | _                => None
  end.

Definition compute_code_def (f : function) :=
  PTree.fold
    (fun acc pc ins =>
      match defined_var ins with
      | Some r => PTree.set r pc acc
      | None   => acc
      end)
    (fn_code f).

Definition compute_phi_def (f : function) :=
  PTree.fold
   (fun acc pc phib =>
     fold_left
       (fun acc phi =>
       match phi with
       | Iphi args dst =>
           PTree.set dst pc acc
       end)
       phib acc)
   (fn_phicode f).

Definition compute_parc_def (f : function) :=
  PTree.fold
   (fun acc pc parcb =>
     fold_left
       (fun acc parc =>
       match parc with
       | Iparcopy src dst =>
           PTree.set dst pc acc
       end)
       parcb acc)
   (fn_parcopycode f).

Definition get_all_def f :=
  PTree.empty node
  @@ compute_code_def f
  @@ compute_phi_def f
  @@ compute_parc_def f.

Definition compute_def (f : function) all_defs :=
  fun r =>
    match PTree.get r all_defs with
    | Some d => d
    | None => fn_entrypoint f
    end.

(** ** gather extern parameters *)
Definition def_set defs :=
  List.fold_right SSARegSet.add SSARegSet.empty defs.

Definition get_ext_params f (all_defs : PTree.t positive)  :=
  SSARegSet.union
    (SSARegSet.diff
      (search_used f)
      (def_set (map fst (PTree.elements all_defs))))
    (param_set f).

(** ** Coalescing classes construction in OCaml. Validated. *)
Parameter build_coalescing_classes_extern :
  function -> (reg -> reg -> bool) -> (reg -> reg) * (PTree.t (list reg)).

(** ** Checker for CSSA value computation *)
Definition check_cssaval_ins (elems : list (node * instruction)) (get_cssaval : reg -> reg) : bool :=
  fold_left
    (fun acc pcins =>
      if negb acc then false
      else match snd pcins with
      | Iop Omove (src :: nil) dst _ => peq (get_cssaval src) (get_cssaval dst)
      | Iop _ _ dst _ => peq (get_cssaval dst) dst
      | Iload _ _ _ dst _ => peq (get_cssaval dst) dst
      | Icall _ _ _ dst _ => peq (get_cssaval dst) dst
      | Ibuiltin _ _ (BR dst) _ => peq (get_cssaval dst) dst
      | _ => true
      end)
    elems true.

Definition check_cssaval_parcb (parcbs : list (node * parcopyblock)) (get_cssaval : reg -> reg) : bool :=
  fold_left
    (fun acc pcparcb =>
      if negb acc then false
      else forallb
        (fun parc =>
          match parc with
          | Iparcopy src dst =>
              peq (get_cssaval src) (get_cssaval dst)
          end)
        (snd pcparcb))
    parcbs
    true.

Definition check_cssaval_phib (phibs : list (node * phiblock)) (get_cssaval : reg -> reg) : bool :=
  fold_left
    (fun acc pcphib =>
      if negb acc then false
      else forallb
        (fun phi =>
          match phi with
          | Iphi args dst => peq (get_cssaval dst) dst
          end)
        (snd pcphib))
    phibs
    true.

Definition check_cssaval_ext_params (ext_params : list reg) (get_cssaval : reg -> reg) : bool :=
  forallb (fun param => peq (get_cssaval param) param) ext_params.

Definition check_cssaval (f : function)
    (get_cssaval : reg -> reg) ext_params : bool :=
  check_cssaval_ins (PTree.elements (fn_code f)) get_cssaval
  && check_cssaval_parcb (PTree.elements (fn_parcopycode f)) get_cssaval
  && check_cssaval_phib (PTree.elements (fn_phicode f)) get_cssaval
  && check_cssaval_ext_params (SSARegSet.elements ext_params) get_cssaval.

Parameter compute_cssaval_function : function -> (reg -> reg).

Definition compute_ninterfere f all_defs ext_params :=
  let def := compute_def f all_defs in
  match CSSAlive.analyze f with
  | None => Errors.Error (Errors.msg "live analysis failed")
  | Some live =>
      let cssaval := compute_cssaval_function f in
      if negb (check_cssaval f cssaval ext_params)
      then Errors.Error (Errors.msg "compute_cssaval")
      else
        Errors.OK
          (fun r1 r2 =>
            peq (cssaval r1) (cssaval r2)
            ||
              let '(d1, d2) := (def r1, def r2) in
              negb
                (peq d1 d2 
                     || SSARegSet.mem r1 (PMap.get d2 live) 
                     || SSARegSet.mem r2 (PMap.get d1 live)))
  end.

(** ** Validation of congruence classes, naive algorithm *)
Fixpoint check_interference_with_class (r : reg) (class : list reg) ninterf :=
  match class with
  | nil => true
  | a :: t =>
      ninterf r a && check_interference_with_class r t ninterf
  end.

Fixpoint check_interference_in_class (class : list reg) ninterf :=
  match class with
  | nil => true
  | a :: t =>
      check_interference_with_class a t ninterf &&
      check_interference_in_class t ninterf
  end.

Definition mem_class_reg regrepr classes r : bool :=
  match PTree.get (regrepr r) classes with
  | Some class => In_reg r class
  | None => peq r (regrepr r)
  end.

Definition mem_class_regs regrepr classes reglist :=
  forallb (mem_class_reg regrepr classes) reglist.

Definition check_coalescing_classes regrepr classes ninterf (all_defs : PTree.t positive) ext_params :=
  forallb (fun class => check_interference_in_class class ninterf) (map snd (PTree.elements classes)) &&
  mem_class_regs regrepr classes (map fst (PTree.elements all_defs)) &&
  mem_class_regs regrepr classes (SSARegSet.elements ext_params).

(** ** Check that phi_ressources are correctly mapped to destinations *)
Definition check_phi_ressources_coalescing regrepr phi :=
  match phi with
  | Iphi args dst =>
      forallb (fun arg => peq (regrepr arg) (regrepr dst)) args
  end.

Definition check_cssa_coalescing_in_phib regrepr phib :=
  forallb (check_phi_ressources_coalescing regrepr) phib.

Definition check_cssa_coalescing_in_phicode regrepr f :=
  forallb (check_cssa_coalescing_in_phib regrepr)
    (map snd (PTree.elements (fn_phicode f))).

(** ** RTLpar generation functions *)

Definition compute_regrepr (f : function) :=
  let all_defs := get_all_def f in
  let ext_params := get_ext_params f all_defs in
  match compute_ninterfere f all_defs ext_params with
  | Errors.Error m => Errors.Error m
  | Errors.OK ninterf =>
      match build_coalescing_classes_extern f ninterf with
      | (regrepr, classes) =>
          if check_coalescing_classes regrepr classes ninterf all_defs ext_params &&
            check_cssa_coalescing_in_phicode regrepr f
          then Errors.OK regrepr
          else Errors.Error (Errors.msg "check_coalescing_classes")
      end
  end.

Definition transl_instruction regrepr ins :=
  match ins with
  | Inop s => Inop s
  | Iop op args res s => Iop op (map regrepr args) (regrepr res) s
  | Iload chunk addr args dst s => Iload chunk addr (map regrepr args) (regrepr dst) s
  | Istore chunk addr args src s => Istore chunk addr (map regrepr args) (regrepr src) s
  | Icall sig (inl r) args res s => Icall sig (inl (regrepr r)) (map regrepr args) (regrepr res) s
  | Icall sig os args res s => Icall sig os (map regrepr args) (regrepr res) s
  | Itailcall sig (inl r) args => Itailcall sig (inl (regrepr r)) (map (regrepr) args)
  | Itailcall sig os args => Itailcall sig os (map regrepr args)
  | Ibuiltin ef args res s => Ibuiltin ef (map (map_builtin_arg regrepr) args) (map_builtin_res regrepr res) s
  | Icond cond args ifso ifnot => Icond cond (map regrepr args) ifso ifnot
  | Ijumptable arg tbl => Ijumptable (regrepr arg) tbl
  | Ireturn None => Ireturn None
  | Ireturn (Some arg) => Ireturn (Some (regrepr arg))
  end.

Definition transl_parcb regrepr (parcb : parcopyblock) :=
  map (fun parc =>
    match parc with
    | Iparcopy src dst =>
        Iparcopy (regrepr src) (regrepr dst)
    end)
    parcb.

Definition transl_code (regrepr : reg -> reg) (code : code) :=
  PTree.map1 (transl_instruction regrepr) code.

Definition transl_parcopycode (regrepr : reg -> reg) (parcode : parcopycode) :=
  PTree.map1 (transl_parcb regrepr) parcode.

(** ** Post processing *)

Fixpoint parcb_cleanup (parcb : parcopyblock) :=
  match parcb with
  | nil => nil
  | Iparcopy src dst :: parcb =>
      if peq src dst then parcb_cleanup parcb
      else Iparcopy src dst :: parcb_cleanup parcb
  end.

Definition parcopycode_cleanup (parcode : parcopycode) :=
  PTree.map1 parcb_cleanup parcode.

(** ** The transformation *)

Definition transl_function (f : CSSA.function) :=
  match compute_regrepr f with
  | Errors.Error m => Errors.Error m
  | Errors.OK regrepr =>
      Errors.OK
        (RTLpar.mkfunction
          f.(fn_sig)
          (map regrepr f.(fn_params))
          f.(fn_stacksize)
          (transl_code regrepr f.(fn_code))
          (parcopycode_cleanup (transl_parcopycode regrepr f.(fn_parcopycode)))
          f.(fn_entrypoint))
  end.

Definition transl_fundef :=
  transf_partial_fundef transl_function.

Definition transl_program (p: CSSA.program) : Errors.res RTLpar.program :=
  transform_partial_program transl_fundef p.

End TRANSFORMATION.
