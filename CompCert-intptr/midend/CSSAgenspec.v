(* Specification of CSSApargen.v transformation *)
Require Import Coqlib.
Require Import Maps.
Require Import CSSA.
Require Import SSA.
Require Import CSSAgen.
Require Import Kildall.
Unset Allow StrictProp.

Inductive unique_def_phib_spec : phiblock -> Prop :=
| unique_def_phib_spec_nil:
    unique_def_phib_spec nil
| unique_def_phib_spec_cons:
    forall args dst phib,
    (forall args' dst',
       In (Iphi args' dst') phib ->
       dst <> dst') ->
    unique_def_phib_spec phib ->
    unique_def_phib_spec (Iphi args dst :: phib).

(* Remark: cssa wellformedness preservation isn't specified here *)

Inductive equiv_phib_spec (maxreg: positive) (k : nat) :
  phiblock -> parcopyblock -> phiblock -> parcopyblock -> Prop :=
| equiv_phib_spec_nil :
    equiv_phib_spec maxreg k nil nil nil nil
| equiv_phib_spec_cons :
    forall arg arg' args args' dst dst'
    phib parcb phib' parcb',
    nth_error args k = Some arg ->
    nth_error args' k = Some arg' ->

    (* parallel copies freshness properties *)
    (forall args'' arg'' dst'', In (Iphi args'' dst'') phib' ->
      nth_error args'' k = Some arg'' ->
      arg' <> arg'') ->
    (forall args'' dst'', In (Iphi args'' dst'') phib' ->
      dst'' <> dst') ->
    (forall args'' dst'', In (Iphi args'' dst'') phib' ->
      arg' <> dst'') ->

    (Ple arg maxreg) ->
    (Ple dst maxreg) ->
    (Plt maxreg arg') ->
    (Plt maxreg dst') ->

    equiv_phib_spec maxreg k phib parcb phib' parcb' ->
    equiv_phib_spec maxreg k
      (Iphi args dst :: phib) (Iparcopy arg arg' :: parcb)
      (Iphi args' dst' :: phib') (Iparcopy dst' dst :: parcb').


Inductive equiv_phib (maxreg: positive) (k : nat) :
  phiblock -> parcopyblock -> phiblock -> parcopyblock -> Prop :=
| equiv_phib_nil :
    equiv_phib maxreg k nil nil nil nil
| equiv_phib_cons :
    forall arg arg' args args' dst dst'
    phib parcb phib' parcb',
    nth_error args k = Some arg ->
    nth_error args' k = Some arg' ->

    (* parallel copies freshness properties *)
    (forall args'' arg'' dst'', In (Iphi args'' dst'') phib' ->
      nth_error args'' k = Some arg'' ->
      arg' <> arg'') ->
    (forall args'' dst'', In (Iphi args'' dst'') phib' ->
      dst'' <> dst') ->
    (forall args'' dst'', In (Iphi args'' dst'') phib' ->
      arg' <> dst'') ->

    (* corollaries of preceding properties *)
    (forall args'' dst'', In (Iphi args'' dst'') phib' ->
      arg <> dst'') ->
    (forall arg'' dst'', In (Iparcopy arg'' dst'') parcb ->
      arg <> dst'') ->
    (forall arg'' dst'', In (Iparcopy arg'' dst'') parcb ->
      arg' <> dst'') ->
    (forall arg'' dst'', In (Iparcopy arg'' dst'') parcb' ->
      dst' <> arg'') ->
    (forall arg'' dst'', In (Iparcopy arg'' dst'') parcb' ->
      dst' <> dst'') ->

    (* wf_ssa *)
    (forall arg'' dst'', In (Iparcopy arg'' dst'') parcb' ->
      dst <> dst'') ->

    (Ple arg maxreg) ->
    (Ple dst maxreg) ->
    (Plt maxreg arg') ->
    (Plt maxreg dst') ->

    equiv_phib maxreg k phib parcb phib' parcb' ->
    equiv_phib maxreg k
      (Iphi args dst :: phib) (Iparcopy arg arg' :: parcb)
      (Iphi args' dst' :: phib') (Iparcopy dst' dst :: parcb').

Variant cssa_spec
    (maxreg : positive)
    (preds : (PTree.t (list node)))
    (ssa_code: code)
    (ssa_pcode: phicode) (cssa_pcode: phicode)
    (cssa_parcopycode: parcopycode)
    (pc: node) (k: nat)
    : Prop :=
| cssa_spec_no_jp :
    ssa_pcode ! pc = None ->
    cssa_spec maxreg preds ssa_code ssa_pcode cssa_pcode
      cssa_parcopycode pc k
| cssa_spec_jp_invalid_k :
    forall phib lpreds,
    ssa_pcode ! pc = Some phib ->
    preds ! pc = Some lpreds ->
    nth_error lpreds k = None ->
    cssa_spec maxreg preds ssa_code ssa_pcode cssa_pcode
      cssa_parcopycode pc k
| cssa_spec_jp_pred_k :
    forall pred phib phib' parcb parcb',
    ssa_pcode ! pc = Some phib ->
    ssa_code ! pred = Some (Inop pc) ->
    cssa_pcode ! pc = Some phib' ->
    index_pred preds pred pc = Some k ->
    cssa_parcopycode ! pred = Some parcb ->
    cssa_parcopycode ! pc = Some parcb' ->
    equiv_phib_spec maxreg k phib parcb phib' parcb' ->
    cssa_spec maxreg preds ssa_code ssa_pcode cssa_pcode
      cssa_parcopycode pc k.

Definition get_preds f :=
  make_predecessors (fn_code f) successors_instr.

Definition normalized_jp (f : SSA.function) :=
  forall pc preds,
  (fn_phicode f) ! pc <> None ->
  (get_preds f) ! pc = Some preds ->
  forall pred,
  In pred preds ->
  (fn_phicode f) ! pred = None.

Definition inop_in_jp (f : SSA.function) :=
  forall pc,
  (fn_phicode f) ! pc <> None ->
  exists succ,
  (fn_code f) ! pc = Some (Inop succ).

Variant tr_function: SSA.function -> CSSA.function -> Prop :=
| tr_function_intro:
    forall f init lp s incr preds,
    (init,lp) = init_state f ->
    wf_ssa_function f ->
    normalized_jp f ->
    preds = make_predecessors (fn_code f) successors_instr ->
    mfold_unit 
      (copy_node preds (fn_code f) (fn_phicode f))
      lp init = OK tt s incr ->
    s.(st_parcopycode) ! (fn_entrypoint f) = None ->
    inop_in_jp f ->
    tr_function f
      (CSSA.mkfunction
        f.(SSA.fn_sig)
        f.(SSA.fn_params)
        f.(SSA.fn_stacksize)
        f.(SSA.fn_code)
        s.(st_phicode)
        s.(st_parcopycode)
        f.(SSA.fn_entrypoint)).

Variant transl_function_spec: SSA.function -> CSSA.function -> Prop :=
| transl_function_spec_intro:
    forall f tf preds,
    normalized_jp f ->
    preds = make_predecessors (fn_code f) successors_instr ->
    (forall pc ins k,
      (fn_code f) ! pc = Some ins ->
      cssa_spec 
        (get_maxreg f)
        preds (fn_code f)
        (fn_phicode f) (CSSA.fn_phicode tf)
        (CSSA.fn_parcopycode tf) pc k) ->
    (forall pc phib,
      (fn_phicode f) ! pc = Some phib ->
      unique_def_phib_spec phib) ->
    (CSSA.fn_parcopycode tf) ! (fn_entrypoint f) = None ->
    inop_in_jp f ->
    transl_function_spec f tf.
