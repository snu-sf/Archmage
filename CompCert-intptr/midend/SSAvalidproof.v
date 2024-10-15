(** The specification of the validation algorithm, given in terms of
    the type system in [SSAvalidspec] is proved to preserve the
    semantics of program. *) 

Require Import Coq.Unicode.Utf8.
Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Classical.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Values.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import Integers.
Require Import PointerOp Simulation RTLdfsD SSAD sflib.
Require Import RTL RTLdfs.
Require Import Kildall.
Require Import KildallComp.
Require Import Conventions.
Require Import Utils.
Require Import RTLutils.
Require RTLdfsgen.
Require Import SSA.
Require Import SSAutils.
Require Import SSAvalid.  
Require Import SSAvalidspec.
Require Import SSAvalidator_proof.  
Require Import Utilsvalidproof.
Require Import LightLive.
Require Import Bijection.
Require Import Classical.
From Paco Require Import paco.

Unset Allow StrictProp.

(** * Some hints and tactics *)
Ltac elimAndb :=
  match goal with
  | [ H: _ && _ = true |- _ ] =>
      elim (andb_prop _ _ H); clear H; intros; elimAndb
  | _ =>
      idtac
  end.

Ltac conv := simpl erase_reg in *.

Global Hint Constructors rtl_cfg: core.
Global Hint Constructors use_rtl_code: core.
Global Hint Constructors wf_live: core.
Global Hint Constructors RTLutils.assigned_code_spec: core.
Global Hint Constructors SSA.assigned_code_spec: core.
Global Hint Extern 4 (In _ (RTLdfs.successors_instr _)) => simpl RTLdfs.successors_instr: core.
Global Hint Extern 4 (In _ (SSA.successors_instr _)) => simpl SSA.successors_instr: core.

Ltac well_typed :=
  match goal with
    | [ Hwt : wt_instr _ _ _ _ |- _ ] => inv Hwt
  end.


(** * Generated SSA functions are well typed, and well formed *)
Section FUNC.

Variable f: RTLdfs.function.
Variable tf: SSA.function.

Hypothesis HWF_DFS : RTLdfsgen.wf_dfs_function f.
Hypothesis TRANSF_OK : SSAvalid.transf_function f = OK tf.

Lemma WELL_TYPED : 
  exists live, 
    (let '(size,def,def_phi) := extern_gen_ssa f (fun pc => Lin f pc (Lout live)) in
    typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf)
    /\ wf_live f (Lout live).
Proof.
  intros. 
  unfold transf_function in  TRANSF_OK. 
  monadInv TRANSF_OK.
  exists x.
  destruct (extern_gen_ssa f (fun pc => Lin f pc (Lout x))) as [[size0 def] def_phi]. 
  split ; auto.
  unfold get_option in EQ.
  case_eq (LightLive.analyze f) ; intros ; rewrite H in * ; inv EQ.
  exploit live_wf_live ; eauto.
Qed.  

Lemma HWF : wf_ssa_function tf.
Proof.
  eapply transf_function_wf_ssa_function ; eauto.
Qed.

End FUNC.

(** * Semantics preservation *)
Require Import Linking.
Section PRESERVATION.

  Definition match_prog (p: RTLdfs.program) (tp: SSA.program) :=
  match_program (fun cu f tf => transf_fundef f = Errors.OK tf) eq p tp.

  Lemma transf_program_match:
    forall p tp, transf_program p = OK tp -> match_prog p tp.
  Proof.
    intros. apply match_transform_partial_program; auto.
  Qed.

  Section CORRECTNESS.
    
  Variable prog: RTLdfs.program.
  Variable tprog: SSA.program.
  
  Hypothesis TRANSL_PROG: match_prog prog tprog.
  Hypothesis WF_DFS_PROG: RTLdfsgen.wf_dfs_program prog.

  Let ge : RTLdfs.genv := Genv.globalenv prog.
  Let tge : SSA.genv := Genv.globalenv tprog.

  Let sem := RTLdfs.semantics prog.
  Let tsem:= SSA.semantics tprog.
  
  Import RTLdfsproof.
    
  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof.
    apply (Genv.find_symbol_transf_partial TRANSL_PROG). 
  Qed.

  Lemma match_prog_wf_ssa : wf_ssa_program tprog.
  Proof.
    red. intros.
    red in  WF_DFS_PROG.
    inv TRANSL_PROG.
    intuition. revert H0 H WF_DFS_PROG.
    induction 1; intros.
    - inv H.
    - inv H1.      
      + inv H. inv H4.
        { destruct f1 ; simpl in * ; try constructor; auto.
          * monadInv H7.
            constructor.
            eapply HWF; eauto.
            destruct a1, g.
            exploit (WF_DFS_PROG (Internal f0) i); eauto.
            simpl in * ; eauto.
            left. inv H; simpl in *; auto. 
            intros. inv H1; auto.
            simpl in *. inv H.
          * monadInv H7.
            constructor.
        }
      + eapply IHlist_forall2; eauto.
  Qed.
  
  Lemma function_ptr_translated:
    forall (b: block) (f: RTLdfs.fundef),
      Genv.find_funct_ptr ge b = Some f ->
      exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
  Proof.
    apply (Genv.find_funct_ptr_transf_partial TRANSL_PROG).
  Qed.

  Lemma functions_translated:
    forall (v: val) (f: RTLdfs.fundef),
      Genv.find_funct ge v = Some f ->
      exists tf, Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
  Proof.
    apply (Genv.find_funct_transf_partial TRANSL_PROG). 
  Qed.

  Lemma sig_function_translated:
  forall f tf,
    transf_function f = OK tf ->
    SSA.fn_sig tf = RTLdfs.fn_sig f.
  Proof.
    intros.
    monadInv H.
    case_eq (extern_gen_ssa f (fun pc => Lin f pc (Lout x))) ; intros [size def] def_phi Hssa ; rewrite Hssa in *.    
    unfold typecheck_function in EQ0. 
    destruct Bij.valid_index; try congruence.
    destruct andb; try congruence.
    destruct check_function_inv.
    destruct fold_left.
    destruct p as [[G newcode] juncpoints].
    monadInv EQ0.
    destruct compute_test_dom.
    destruct check_unique_def; simpl in EQ2; try congruence. 
    destruct check_code_at_phipoints; simpl in EQ2; try congruence. 
    inv EQ2; auto.
    congruence.
    congruence.
    congruence.
  Qed.
  
  Lemma sig_fundef_translated:
    forall f tf,
      transf_fundef f = OK tf ->
      SSA.funsig tf = RTLdfs.funsig f.
  Proof.
    intros.
    destruct f. 
    - monadInv H.
      simpl. eapply sig_function_translated; eauto.
    - monadInv H ; auto.
  Qed.

  Lemma senv_preserved:
    Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
  Proof.
    apply (Genv.senv_transf_partial TRANSL_PROG).
  Qed.

  Lemma same_public:
  prog_public prog = prog_public tprog.
  Proof. inv TRANSL_PROG. des; eauto. Qed.

  Lemma spec_ros_r_find_function:
    forall rs rs' f r r' m,
      rs#r = rs'# r' ->
      RTLdfs.find_function ge (RTLdfs.ros_to_vos m (inl _ r) rs) rs = Some f ->
      exists tf,
        SSA.find_function tge (SSA.ros_to_vos m (inl _ r') rs') rs' = Some tf
        /\ transf_fundef f = OK tf.
  Proof.
    intros. ss. des_ifs.
    - ss. exploit (functions_translated (Vptr b (Ptrofs.repr z))); eauto.
    - ss. exploit (functions_translated (Vptr b i)); eauto.
  Qed.
  
  Lemma spec_ros_id_find_function:
    forall rs rs' f id m,
      RTLdfs.find_function ge (RTLdfs.ros_to_vos m (inr _ id) rs) rs = Some f ->
      exists tf,
        SSA.find_function tge (SSA.ros_to_vos m (inr _ id) rs') rs' = Some tf
        /\ transf_fundef f = OK tf.
  Proof.
    intros.
    simpl in *.
    case_eq (Genv.find_symbol ge id) ; intros.
    rewrite H0 in H.
    rewrite symbols_preserved in * ; eauto ; rewrite H0 in *.
    exploit function_ptr_translated; eauto.
    rewrite H0 in H ; inv H.
  Qed.

  Lemma spec_ros_find_function:
  forall size rs rs' f ros ros' m,
    check_ros_spec size ros ros' ->
    (forall r r', ros = (inl ident (erase_reg size r)) -> ros' = (inl ident r') -> rs#(erase_reg size r) = rs'# r') ->
    RTLdfs.find_function ge (RTLdfs.ros_to_vos m ros rs) rs = Some f ->
    exists tf,
      SSA.find_function tge (SSA.ros_to_vos m ros' rs') rs' = Some tf
      /\ transf_fundef f = OK tf.
    Proof.
      intros.
      case_eq ros; intros.
      - subst. inv H.
        eapply spec_ros_r_find_function in H1; eauto.
      - inv H; inv H3.        
        eapply spec_ros_id_find_function with (rs:= rs); eauto.
    Qed.

  Lemma instr_at:
    forall size f tf pc rinstr Γ live,
      check_function_spec size f live tf Γ  ->
      (RTLdfs.fn_code f)!pc = Some rinstr ->
      exists pinstr, 
        (SSA.fn_code tf)!pc = Some pinstr /\
        check_instrs_spec size tf rinstr pinstr.
  Proof.
    intros. inv H. 
    destruct H1 as [Hsig [Hstack [Herased [Hdef [Hphipar Hnodup]]]]].
    assert (Herased2:= erased_funct_erased_instr _ pc f tf rinstr Herased H0).
    destruct Herased2 as [pinstr [Htf Hrpinstr]].
    exists pinstr. split; eauto.
    rewrite Hrpinstr in *. 
    eapply check_instr_spec_erase; eauto.
  Qed.
    
  Ltac error pc :=
    (match goal with
       | [ H1: (fn_phicode _) ! pc = Some _,
         H2: ~ join_point pc _
         |- _ ] =>   elim H2 ; eapply phicode_joinpoint ; eauto
       | [ H1: (fn_phicode ?tf) ! pc = None ,
         H2: join_point pc _,
         HWF: wf_ssa_function ?tf
         |- _ ] =>   eelim (nophicode_nojoinpoint tf HWF pc); eauto
     end).

  Ltac error_struct tf pc pc' :=
    (match goal with
       | [ H1 : (fn_code tf) ! pc = Some _ ,
         H2 : (fn_phicode tf) ! pc' = Some _,
         HWF: wf_ssa_function ?tf
         |- _ ] =>
       let Hcont := fresh "Hcont" in
         (exploit (elim_structural tf HWF pc pc'); eauto ; intros Hcont ; inv Hcont)
     end).
  
  Ltac instr_succ pc pc' Hi :=
    match goal with
      | [ H1 : (fn_code ?tf) ! pc = Some _,
        HWF: wf_ssa_function ?tf
        |- _ ] =>
      assert (Hi : exists i, (fn_code tf) ! pc' = Some i) by
        (eapply (SSA.fn_code_closed tf HWF pc pc'); eauto;  (simpl; auto));
        destruct Hi as [instr' Hinstr'] ;
          destruct (join_point_exclusive tf HWF pc' instr' Hinstr'); (try (error pc'); try (error_struct tf pc pc'))
    end.

  (** ** Simulation relation *)

  (** Matching relation for stackframes *)
  Inductive match_stackframes : list RTLdfs.stackframe -> list SSA.stackframe -> Prop :=
  | match_stackframes_nil: match_stackframes nil nil 
  | match_stackframes_cons: 
    forall res f sp pc rs s tf rs' ts Γ live size
      (WF: wf_ssa_function tf),
      (match_stackframes s ts) ->
      (check_function_spec size f live tf Γ) ->
      (wf_live f (Lout live)) ->
      (∀ j ins, (RTLdfs.fn_code f) ! j = Some ins → (RTLutils.cfg (RTLdfs.fn_code f) ** ) (RTLdfs.fn_entrypoint f) j) ->
      (fn_phicode tf) ! pc = None ->
      get_index size res = (Γ pc) (erase_reg size res) ->
      (forall r, r <> (erase_reg size res) ->
                 Regset.In r (Lin f pc (Lout live)) ->
                 Bij.valid_index size (Γ pc r) = true ->
                 rs#r = rs'# (Bij.pamr size (r,Γ pc r))) ->
      (Bij.valid_reg_ssa size res = true) ->
      match_stackframes 
      ((RTLdfs.Stackframe (erase_reg size res) f sp pc rs) :: s)
      ((SSA.Stackframe res tf sp pc rs') :: ts).

  (** Agreement between values of registers wrt a register mapping *)
  Definition agree (size: nat) (β: Registers.reg -> index) (rs: RTLdfs.regset) (rps: SSA.regset) (live: Regset.t) : Prop :=
    forall r,
      Regset.In r live ->
      Bij.valid_index size (β r) = true ->
      rs # r  = rps # (Bij.pamr size (r, β r)).
  
  Arguments Lout [A].
  Reserved Notation "s ≃ s'" (at level 40).
  
  (** Matching relation for states *)
  Variant match_states : RTLdfs.state -> SSA.state -> Prop :=
  | match_states_reg: 
    forall s f sp pc rs m ts tf  rs'  Γ live size
      (STACKS: match_stackframes s ts)
      (SPEC: check_function_spec size f live tf Γ)
      (WFDFS: (∀ j ins, (RTLdfs.fn_code f) ! j = Some ins → (RTLutils.cfg (RTLdfs.fn_code f) ** ) (RTLdfs.fn_entrypoint f) j))
      (WF: wf_ssa_function tf)
      (LIVE: wf_live f (Lout live))
      (AG: agree size (Γ pc)  rs rs' (Lin f pc (Lout live))),
      (RTLdfs.State s f sp pc rs m) ≃ (SSA.State ts tf sp pc rs' m)
  | match_states_return: 
    forall s res m ts 
      (STACKS: match_stackframes s ts),
      (RTLdfs.Returnstate s res m) ≃ (SSA.Returnstate ts res m)
  | match_states_call:
    forall s f args m ts tf
      (STACKS: match_stackframes s ts)
      (WFDFS: RTLdfsgen.wf_dfs_fundef f)
      (TRANSF: transf_fundef f = OK tf),
      (RTLdfs.Callstate s f args m) ≃ (SSA.Callstate ts tf args m)
   where "s ≃ t" := (match_states s t).
  Hint Constructors match_states: core.  

  (** ** Auxiliary lemmas about [agree] preservation *)
  
  Import DLib.  

  Lemma phistore_preserve_agree: 
    forall (tf: function) rs rs' k pc0 pc block G (v:positive) live size f
      (LIVE: forall x, Regset.In x (Lin f pc (Lout live)) → Regset.In x (Lin f pc0 (Lout live)))
      (CFNS: check_phi_params_spec tf)
      (UDEF:  unique_def_spec tf)
      (NODUP: check_no_duplicates_spec size tf )
      (PHI: (fn_phicode tf)! pc = Some block)
      (PRED: index_pred (make_predecessors (fn_code tf) successors_instr) pc0 pc = Some k)
      (AG: agree size (G pc0) rs rs' (Lin f pc0 (Lout live)))
      (WTEDGE: wt_edge tf size (Lin f pc (Lout live)) G pc0 pc),
      agree size (G pc) rs (phi_store  k block rs') (Lin f pc (Lout live)).
  Proof.
  intros.
  unfold agree in *. intros x Hlive Hvalid.
  generalize (erased_reg_assigned_dec size x block); intro Hx.
  destruct Hx as [Hx1 | Hx2 ]; invh wt_edge; allinv ; try congruence.  
  
  - (* there is a j st x_j is assigned in block *)
    inv Hx1. invh and. 
    inv H0. 
    erewrite AG ; eauto.
    + unfold erase_reg. 
      destruct (Bij.rmap size x0) as (xx & j) eqn:EQ. 
      simpl in *.
      erewrite phi_store_copy with (args:= x); eauto.
      * eapply check_udef_spec_no_dup; eauto.
      * exploit check_udef_spec_no_dup; eauto. intros.    
        eapply UDEF; eauto. 
      * split.
        -- inv WTPHID; erewrite ASSIG; go.
           rewrite <- EQ at 1.
           rewrite Bij.BIJ2; auto.
           eapply VALIDR; eauto; go.
      
        -- inv WTPHID0.
           exploit USES; eauto. intros PHIU.
           exploit CFNS ; eauto. intros NTH. 
           exploit @nth_okp_exists; eauto. intros [xarg Hxarg].
           exploit index_pred_some_nth; eauto. intros.
           exploit (@list_map_nth_some _ _ G); eauto. intros.
           eapply phiu_nth in PHIU ; eauto.
           destruct PHIU as (HVALIDR & xargs & HEQ & HG & HVALIDI).
           subst.
           rewrite <- HEQ at 1.
           rewrite Bij.BIJ2; auto.
    + unfold erase_reg in *. 
      destruct (Bij.rmap size x0) as (xx & j) eqn:EQ. 
      inv WTPHID0.
      exploit USES; eauto. intros PHIU.
      exploit CFNS ; eauto. intros NTH. 
      exploit @nth_okp_exists; eauto. intros [xarg Hxarg].
      exploit index_pred_some_nth; eauto. intros.
      exploit (@list_map_nth_some _ _ G); eauto. intros.
      eapply phiu_nth in PHIU ; eauto.
      destruct PHIU as (HVALIDR & xargs & HEQ & HG & HVALIDI).
      subst. eauto.

  - (* no x_j is assigned in the block *)
    erewrite phi_store_notin_preserved; eauto. 
    + rewrite (AG x); eauto.
      * invh wt_phid.
        eelim (NASSIG x); go.
        intros; intro Hcont; eelim Hx2; go.
        econstructor; split; eauto.
        unfold erase_reg. rewrite H. auto.
        
      * invh wt_phid.
        eelim (NASSIG x); go.
        intros; intro Hcont; eelim Hx2; go.
        econstructor; split; eauto.
        unfold erase_reg. rewrite H. auto.        
    + intros; intro Hcont; eelim Hx2; go.
      exists (Bij.pamr size (x, G pc x)).
      split.
      * econstructor; eauto.
      * unfold erase_reg.
        rewrite Bij.BIJ1; auto.
Qed.
  
  Lemma update_preserve_agree: forall size rs rs' γi dst v r i live live' γ', 
      Bij.valid_reg_ssa size dst = true ->
      Bij.rmap size dst = (r,i) ->
      agree size γi rs rs' live ->
      (forall x, Regset.In x live' -> (Regset.In x live) \/ x = r) ->
      γ' = (update γi r i) ->
      agree size γ' (rs # r <- v) (rs' # dst <- v) live'.
  Proof.
    intros.
    unfold agree in * ; intros.
    inv H3.
    destruct (peq r0 r).
    - (* r' = r : same value ok *)
      rewrite e in *. 
      unfold update ; rewrite peq_true; auto. 
      subst.
      rewrite <- H0 at 1. rewrite Bij.BIJ2; auto.
      rewrite ! PMap.gss; auto.
    - (* r' <> r : update unchanged *)
      exploit H2 ; eauto.
      intros [Hcase1 | Hcase2].
      + unfold update in *; rewrite peq_false in *; auto.
        rewrite ! PMap.gso; auto.    
        intro. subst.
        rewrite Bij.BIJ1 in H0; [congruence|].
        auto.
      + subst.
        unfold update in *. rewrite peq_true in *; auto.
        rewrite <- H0 at 1.
        rewrite Bij.BIJ2; auto.
        rewrite ! PMap.gss; auto.
  Qed.

Lemma agree_preserve_arg : forall size γ rs rs' arg live,
  Regset.In arg live ->
  agree size γ rs rs' live ->
  Bij.valid_index size (γ arg) = true ->
  rs # arg = rs' # (Bij.pamr size (arg, γ arg)).
Proof.
  intros.
  unfold agree in *.
  rewrite (H0 arg); eauto.
Qed.
  
Lemma agree_preserve_args : forall size γ rs rs' args args'  live,
    (forall arg, In arg args -> Regset.In arg live) ->
    check_args_spec size args args' ->
    (forall ri r i, In ri args' -> Bij.rmap size ri = (r, i) -> γ r = i) ->
    (forall ri, In ri args' -> forall r i, Bij.rmap size ri = (r, i) -> Bij.valid_index size i = true) ->
    (forall ri, In ri args' -> Bij.valid_reg_ssa size ri = true) ->
    agree size γ rs rs' live ->
    rs ## args = rs' ## args'.
Proof.
  induction 2 ; auto.
  intros SPEC VALIDI VALIDR AG.
  simpl; rewrite IHcheck_args_spec; eauto.
  destruct (Bij.rmap size arg) as (r, i) eqn: Heq.
  unfold erase_reg in * ; rewrite Heq in * ; simpl in *.
  cut (rs # r = rs'# arg).
  + intros H4; rewrite H4 ; auto.
  + exploit_dstr (SPEC arg r i);  eauto.
    erewrite AG; eauto.
    rewrite <- Heq at 1.
    rewrite Bij.BIJ2; eauto.    
Qed.

Lemma agree_init_regs_gamma: forall tf Γ params args live size,
  inclist params (fn_params tf) ->
  wf_init size tf Γ ->
  agree size (Γ (fn_entrypoint tf)) (RTLdfs.init_regs args (map (erase_reg size) params)) (init_regs args params) live.
Proof.
  induction params; intros.
  - (* nil *) simpl. unfold agree; intros. inv H0; allinv. rewrite PMap.gi; rewrite PMap.gi; auto.
  - (* a::l *)
    case_eq args; intros.
    (* args = nil *) simpl ; unfold agree; intros. rewrite PMap.gi; rewrite PMap.gi; auto.
    (* args = v::l0 *)  
    case_eq (Bij.rmap size a); intros.
    unfold agree; intros.
    set (mg := Γ (fn_entrypoint tf) r0) in *.
    simpl in |- * ; unfold erase_reg at 1 ; rewrite H2 in * ;  simpl in |- *.
    
    assert (Hsuff: inclist params (fn_params tf)) by (eapply inclist_indu ; eauto).
    
    assert (IHL := IHparams l live size Hsuff H0).
    generalize H0 ; intros WFINIT.
    inv H0; allinv. 
    assert (Hina: In a (fn_params tf)). eapply inclist_cons_in; eauto.
    assert (ext_params tf a) by eauto.
    exploit (H5 a); eauto. intros [HVALID H1].
    destruct H1.
    rewrite H1 in H2. inv H2.
    destruct (peq r r0).
    + (* r = r0 *) inv e.
      unfold mg. rewrite <- H1 at 1.
      rewrite Bij.BIJ2; auto.
      rewrite PMap.gss; rewrite PMap.gss; auto.
    + (* r <> r0 *)
      rewrite PMap.gso; try rewrite PMap.gso; auto.
      eapply IHparams ; eauto.
      intro; subst. rewrite Bij.BIJ1 in H1. congruence.
      eauto. 
Qed.

Lemma wt_call_agree : forall f tf live size pc fd fn' args'  s ts sp dst pc' x Γ rs rs' ros
  (WFLIVE: wf_live f (Lout live))
  (WF_SSA: wf_ssa_function tf)
  (WFDFS: (∀ j ins, (RTLdfs.fn_code f) ! j = Some ins → (RTLutils.cfg (RTLdfs.fn_code f) ** ) (RTLdfs.fn_entrypoint f) j)),
  (RTLdfs.fn_code f) ! pc = Some (RTL.Icall (RTLdfs.funsig fd) ros (map (erase_reg size)  args') (erase_reg size dst) pc') ->
  (fn_code tf) ! pc = Some (Icall (RTLdfs.funsig fd) fn' args' dst pc') ->
  is_edge tf (pc) pc' ->
  index_pred  (make_predecessors (fn_code tf) successors_instr) pc pc' = Some x ->
  agree size (Γ pc) rs rs' (Lin f pc (Lout live)) ->
  unique_def_spec tf ->
  check_function_spec size f live tf Γ ->
  wt_edge tf size (Lin f pc' (Lout live)) Γ pc pc' ->
  match_stackframes s ts->
  match_stackframes (RTLdfs.Stackframe (erase_reg size dst) f sp pc' rs :: s)
  (Stackframe dst tf sp  pc' rs' :: ts).
Proof.
  intros. generalize H6 ; intro HWTE.
  inv HWTE ; allinv ; (case_eq (Bij.rmap size dst); intros).

  - (* match stack frame 1 *)
  eapply match_stackframes_cons; eauto.
  + unfold erase_reg, get_index. rewrite H8. simpl.
    well_typed; allinv.
    * assert (HEQ: (r, i) = (r0, i0)) by congruence. inv HEQ.
      (unfold update in *; simpl; try rewrite peq_true; auto).
    * assert (HEQ: (r, i) = (r0, i0)) by congruence. inv HEQ.
      unfold update. rewrite peq_true; auto.
  + unfold erase_reg; simpl in *. rewrite H8. simpl. 
    intros.
    assert (HGEQ: Γ pc r0 = Γ pc' r0). 
    { well_typed; eauto.
      - assert (HEQ: (r1, i0) = (r, i)) by congruence. inv HEQ.
        unfold update in * ; rewrite peq_false in * ; simpl in *; auto.
      - assert (HEQ: (r1, i0) = (r, i)) by congruence. inv HEQ.
        unfold update in * ; rewrite peq_false in * ; simpl in *; auto.        
    }
    exploit (wf_live_incl f (Lout live) WFLIVE pc pc') ; eauto.
    rewrite <- HGEQ.
    intuition. 
    
    (* eapply agree_preserve_arg with (γ := Γ pc) ; eauto. *)
    (* * (* well_typed; rewrite HGEQ; eauto. *)  *)
    * inv H13; allinv.
      unfold erase_reg in *. rewrite H8 in *. 
      go.
  + well_typed; allinv; eauto.
    
  - (* match stack frame 2 : contradiction, cannot go to a join point with Icall *)
    assert (Hpc' : exists i, (fn_code tf)! pc' = Some i)
      by (eapply SSA.fn_code_closed; eauto).
    destruct Hpc' as (ii & Hi).
    exploit SSAutils.fn_phicode_inv1; eauto.
    intros. 
    assert ((fn_code tf) ! pc = Some (Inop pc')).
    eapply fn_normalized with (pc:= pc) ; eauto.
    unfold successors_list, successors.
    rewrite PTree.gmap1.
    rewrite H0. simpl. auto.
    allinv.
Qed.

Create HintDb agree.
Create HintDb valagree.

Hint Resolve phistore_preserve_agree : agree.
Hint Resolve update_preserve_agree : agree.
Hint Resolve symbols_preserved : valagree.
Hint Resolve eval_addressing_preserved : valagree.
Hint Resolve eval_operation_preserved : valagree.
Hint Resolve agree_preserve_arg : valagree.
Hint Resolve agree_preserve_args : valagree.
Hint Resolve sig_fundef_translated : valagree.

Lemma agree_preserve_builtin_arg : forall size sp m arg v rs,
    eval_builtin_arg ge (λ r : positive, rs # r) sp m arg v ->
    forall γ rs' arg' live,
      arg = (map_builtin_arg (λ a : reg, erase_reg size a) arg') ->
      (forall arg, In arg (params_of_builtin_arg (map_builtin_arg (λ a : reg, erase_reg size a) arg')) -> Regset.In arg live) ->
      (forall ri r i, In ri (params_of_builtin_arg arg') -> Bij.rmap size ri = (r, i)  -> γ r = i) ->
      (forall ri r i, In ri (params_of_builtin_arg arg') -> Bij.rmap size ri = (r,i) -> Bij.valid_index size i = true) ->
      (forall ri, In ri (params_of_builtin_arg arg') -> Bij.valid_reg_ssa size ri = true) ->
      agree size γ rs rs' live ->
      eval_builtin_arg ge (λ r : PMap.elt, rs' !! r) sp m arg' v.
Proof. 
  induction 1; intros; simpl in * ; eauto with barg;
    destruct arg';
    try solve [match goal with
                 id: _ = _ |- _ => inv id
               end; constructor; auto].
  - inv H. 
    destruct (Bij.rmap size x0) as (rx0, ix0) eqn: Hx0.
    unfold erase_reg; rewrite Hx0. simpl.
    rewrite (H4 rx0); eauto with valagree.
    erewrite H1 with (i:= ix0); eauto.
    rewrite <- Hx0 at 1. rewrite Bij.BIJ2.
    constructor. 
    + eapply H3; go. 
    + constructor; auto.
    + eapply H0; simpl; eauto.
      unfold erase_reg; rewrite Hx0. auto. 
    + eapply H2; eauto.
      constructor; auto.
      erewrite H1; eauto.
      constructor; auto.
      
  - inv H1. constructor; eauto.
    + eapply IHeval_builtin_arg1; eauto.
      * intros. eapply H2; eauto. simpl.
        apply in_or_app; eauto.
      * intros. eapply H3; eauto. simpl.
        apply in_or_app; eauto.
      * intros; eapply H4; eauto. simpl.
        apply in_or_app; eauto.
      * intros; eapply H5; eauto. simpl.
        apply in_or_app; eauto.
    + eapply IHeval_builtin_arg2; eauto.
      * intros. eapply H2; eauto. simpl.
        apply in_or_app; eauto.
      * intros. eapply H3; eauto. simpl.
        apply in_or_app; eauto.
      * intros; eapply H4; eauto. simpl.
        apply in_or_app; eauto.       
      * intros; eapply H5; eauto. simpl.
        apply in_or_app; eauto.
  - inv H1.
    constructor; eauto.
    + eapply IHeval_builtin_arg1; eauto.
      * intros. eapply H2; eauto. simpl.
        apply in_or_app; eauto.
      * intros. eapply H3; eauto. simpl.
        apply in_or_app; eauto.
      * intros; eapply H4; eauto. simpl.
        apply in_or_app; eauto.
      * intros; eapply H5; eauto. simpl.
        apply in_or_app; eauto.
    + eapply IHeval_builtin_arg2; eauto.
      * intros. eapply H2; eauto. simpl.
        apply in_or_app; eauto.
      * intros. eapply H3; eauto. simpl.
        apply in_or_app; eauto.
      * intros; eapply H4; eauto. simpl.
        apply in_or_app; eauto.
      * intros; eapply H5; eauto. simpl.
        apply in_or_app; eauto.
Qed.

Lemma agree_preserve_builtin_args : forall size sp m  γ rs rs' args' vargs live,
    eval_builtin_args ge (λ r : positive, rs # r) sp m (map (map_builtin_arg (λ a : reg, erase_reg size a)) args') vargs ->
    (forall arg, In arg (params_of_builtin_args (map (map_builtin_arg (λ a : reg, erase_reg size a)) args')) -> Regset.In arg live) ->
    check_args_spec size (params_of_builtin_args (map (map_builtin_arg (λ a : reg, erase_reg size a)) args')) (params_of_builtin_args args') ->
    (forall ri r i, In ri (params_of_builtin_args args') -> Bij.rmap size ri = (r, i)  -> γ r = i) ->
    (forall ri r i, In ri (params_of_builtin_args args') -> Bij.rmap size ri = (r, i)  -> Bij.valid_index size i = true) ->
    (forall ri, In ri (params_of_builtin_args args') -> Bij.valid_reg_ssa size ri = true) ->
    agree size γ rs rs' live ->
    eval_builtin_args tge (λ r : PMap.elt, rs' !! r) sp m args' vargs.
Proof.
  induction args' ; intros; eauto with barg.
  - simpl in *. invh eval_builtin_args. constructor.
  - simpl in *. invh eval_builtin_args. constructor.
    + eapply eval_builtin_arg_preserved with (ge1:= ge); eauto.
      * apply symbols_preserved.
      * eapply agree_preserve_builtin_arg; eauto.
        -- intros. eapply H0; eauto. simpl.
           apply in_or_app; eauto.
        -- intros. eapply H2; eauto. simpl.
           apply in_or_app; eauto.
        -- intros. eapply H3; eauto. simpl.
           apply in_or_app; eauto.
        -- intros. eapply H4; eauto. simpl.
           apply in_or_app; eauto.
           
    + eapply IHargs'; eauto.
      * intros. eapply H0; eauto.
        apply in_or_app. right; auto.
      * revert H1. clear.
        generalize (params_of_builtin_args (map (map_builtin_arg (λ a0 : reg, erase_reg size a0)) args')).
        generalize (params_of_builtin_args args').
        intros.
        eapply check_args_spec_erased_rwt_iff.
        eapply check_args_spec_erased_rwt_iff in H1.
        { rewrite map_app in H1.
          replace (params_of_builtin_arg (map_builtin_arg (λ a : reg, erase_reg size a) a))
            with (map (erase_reg size) (params_of_builtin_arg a)) in H1.
          - eapply app_inv_head; eauto.
          - clear H1. 
            induction a; simpl; intros; auto.
            + rewrite map_app.
              rewrite IHa1; eauto.
              rewrite IHa2; eauto.
            + rewrite map_app.
              rewrite IHa1; eauto.
              rewrite IHa2; eauto.
        }
      * intros. eapply H2; eauto.
        apply in_or_app. right; auto.
      * intros. eapply H3; eauto.
        apply in_or_app; eauto.
      * intros. eapply H4; eauto.
        apply in_or_app; eauto.
Qed.

(** ** The [match_state] is indeed a simulation relation *)
Lemma transf_initial_states:
  forall st1, RTLdfs.initial_state prog st1 ->
    exists st2, SSA.initial_state tprog st2 /\ st1 ≃ st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated ; eauto. intros [tf [Hfind Htrans]].
  econstructor; split.
  - econstructor.
    assert (MEM: (Genv.init_mem tprog) = Some m0) by (eapply (Genv.init_mem_transf_partial TRANSL_PROG); eauto).
    + apply MEM ; auto.
    + replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
      symmetry; eapply match_program_main; eauto.
    + eauto.
    + rewrite <- H3. apply sig_fundef_translated; auto.
  - eapply match_states_call  ; eauto.
    + constructor.
    + eapply Genv.find_funct_ptr_prop ; eauto.  
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  st1 ≃ st2 -> RTLdfs.final_state st1 r -> SSA.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor.
Qed.

Ltac exploit_hyps SPEC :=
  let Hspec' := fresh "Hspec'" in
  (exploit instr_at; eauto; intros Hinstr;
    destruct Hinstr as [pinstr [Hpinstr Hspec]];
      generalize Hspec; intro Hspec' ; inv Hspec';
        generalize SPEC; intro SPEC'; inv SPEC;
  (match goal with
     | [ H1 : wf_init _ _ _  /\ wt_function _ _ _ _ _ /\ _ |- _ ] => destruct H1 as [Hwfi [[Hwte Hwto] HWL]]
     | _ => idtac
   end);
  (match goal with
     | [ H1 : structural_checks_spec _ _ _ |- _ ] => destruct H1 as [SSIG [SSTACK [SERAS [SUDEF [SPHI SDUP]]]]]; auto
     | _ => idtac
   end)).

Ltac matches pc pc' :=
  (match goal with
     | [ H1: (fn_phicode _) ! pc = Some ?block,
       H2: (fn_phicode _) ! pc' = Some _,
       H3: index_pred _ ?i pc = Some ?k
       |- _ ] => idtac
     | [ H1: (fn_phicode _) ! pc' = Some _ |- _ ] => 
       (econstructor ; eauto)  ; eauto with agree
     |  [ H1: (fn_phicode _) ! pc' = None |- _ ] =>
       (try econstructor ; eauto ; (eauto ; eauto with agree));
       (eauto with agree) ; eauto with agree
   end);
  allinv ; eauto with agree.

Lemma regmap_setres_noBR : forall T vres rs dst,
    (forall r, dst <> BR r) ->
    (@regmap_setres T dst vres rs) = rs.
Proof.
  induction dst ; intros ; simpl in * ; eauto.
  eelim H; eauto.
Qed.

Lemma regmap_setres_erase_noBR : forall size T vres rs dst,
    (forall r, dst <> BR r) ->
    (@regmap_setres T (map_builtin_res (erase_reg size) dst) vres rs) = rs.
Proof.
  induction dst ; intros ; simpl in * ; eauto.
  eelim H; eauto.
Qed.

Lemma transl_step_correct:
  forall s1 t s2, IStep sem s1 t s2 ->
    forall s1', 
      s1 ≃ s1' ->
      exists s2',
        DStep tsem s1' t s2' /\ s2 ≃ s2'.
Proof.
  destruct 1. generalize dependent s2. rename H into INT.
  induction 1; intros s1' MATCH;
    inv MATCH; auto;

  try (try exploit_hyps SPEC;
  try (assert (Hedge : is_edge tf pc pc') by go;
    assert (Hwtedge : wt_edge tf _ (Lin f pc' (Lout live)) Γ pc pc') by eauto);
  (exploit is_edge_pred ; eauto ; intros [x H2] ) ;
  try (
    assert (Hedge0 : is_edge tf pc0 pc) by (eapply pred_is_edge; eauto);
      assert (Hwtedge0 : wt_edge tf _ (Lin f pc' (Lout live)) Γ pc0 pc) by (eauto)
  );
  try (case_eq ((fn_phicode tf)!pc'); intros) ;
  try destruct (join_point_exclusive tf HWF pc')); try (error pc'); try (error_struct tf pc pc');
  try (instr_succ pc pc' Hi ; try (error pc'); try (error_struct tf pc pc')).
  
  - (* nop *)
    (* 1 - from a state with phi-block at pc' : exec phiblock and then instr at pc' *)
    exists (State ts tf sp pc' (phi_store x p rs') m).
    split. DStep_tac. constructor 2; auto. 
    inv Hwtedge; allinv.
    econstructor ; eauto.  
    eapply phistore_preserve_agree  with (pc:= pc') (pc0:= pc) ; eauto. 
    intros. exploit (wf_live_incl f (Lout live) HWL pc pc') ; eauto.
    intuition. inv H5 ; allinv.  
    
  - (* 2 - from a state with no phi-block at pc' *)
    exists (State ts tf sp pc' rs' m).
    split. DStep_tac.  constructor ; auto.
    inv Hwtedge; allinv. well_typed; allinv.
    matches pc pc'. 
    unfold agree in *; intros.
    exploit AG ; eauto. 
    intros. exploit (wf_live_incl f (Lout live) HWL pc pc') ; eauto. 
    intuition. inv H7 ; allinv. 

  - (* op *)
    exists (State ts tf sp pc' (rs'# dst <- v) m).
    split. DStep_tac. econstructor ; eauto.
    inv Hwtedge; allinv.
    well_typed.
    rewrite <- H0. replace (rs'## args') with (rs##args); eauto with valagree.
    { eapply eval_operation_wrapper_preserved. eapply senv_preserved. }
    eapply agree_preserve_args; eauto.
    intros ; exploit (wf_live_use f (Lout live)) ; eauto.

    (inv Hwtedge; allinv; well_typed); matches pc pc'.

    eapply update_preserve_agree ; eauto.
    + rewrite H12. unfold erase_reg. rewrite H12. auto.
    + intros ; exploit (wf_live_incl f (Lout live)) ; eauto. intuition.
      right ; inv H7 ; allinv ; auto.
    + unfold erase_reg. rewrite H12. auto.
      
  - (* load *)
    exists (State ts tf sp pc' (rs'# dst0 <- v) m).
    split. DStep_tac. eapply exec_Iload; eauto.
    inv Hwtedge ; allinv ; well_typed ; rewrite <- H0; replace (rs'## args') with (rs##args); eauto with valagree.
    eapply agree_preserve_args; eauto.
    intros ; exploit (wf_live_use f (Lout live)) ; eauto.
    inv Hwtedge; allinv; well_typed.
    matches pc pc'.
    eapply update_preserve_agree ; eauto.
    + unfold erase_reg. rewrite H14. auto.
    + intros ; exploit (wf_live_incl f (Lout live)) ; eauto. intuition.
      right ; inv H7 ; allinv ; auto.  
    + unfold erase_reg. rewrite H14. auto.
      
  - (* store *)
    exists (State ts tf sp pc' rs' m').
    split.
    + DStep_tac. eapply exec_Istore with (a:= a) ; eauto.
      * inv Hwtedge ; allinv ; well_typed;
        rewrite <- H0; replace (rs'## args') with (rs##args); eauto with valagree.
        eapply agree_preserve_args; eauto.
        intros;  eapply (wf_live_use f (Lout live)) ; eauto. 
      * rewrite <- H1; inv Hwtedge ; allinv ; well_typed.
        replace (rs'!! src0) with (rs#(erase_reg size src0)); eauto with valagree.
        unfold erase_reg ; simpl.
        destruct (Bij.rmap size src0) as (r, p) eqn:EQ ; simpl fst in *. 
        assert (Γ pc r = p) by (exploit H10 ; eauto).
        replace src0 with (Bij.pamr size (r,p)).
        -- rewrite <- H5.
           eapply agree_preserve_arg ; eauto.
           replace r with (erase_reg size src0).
           eapply (wf_live_use f (Lout live)) ; eauto.
           unfold erase_reg; rewrite EQ. auto.
           subst. eapply H14 with (r:= r); eauto.
        -- rewrite <- EQ. rewrite Bij.BIJ2; auto.
    + inv Hwtedge; allinv; well_typed ;  matches pc pc'.
      unfold agree in *; intros. 
      intros ; exploit (wf_live_incl f (Lout live)) ; eauto. intuition.
      eapply AG ; eauto. 
      inv H9 ; allinv.
     
  - (* call *) 
    exploit (spec_ros_find_function size rs rs' fd ros fn') ;eauto.
    + intros. inv H4. inv H6. inv H8.
      destruct (Bij.rmap size r') as (rr', p) eqn:EQ.
      unfold erase_reg. rewrite EQ. simpl.
      replace r' with (Bij.pamr size (rr',p)).
      * inv Hwtedge; allinv; well_typed. 
        replace p with (Γ pc rr').
        -- eapply agree_preserve_arg; eauto.
           replace rr' with (erase_reg size r').
           eapply (wf_live_use f (Lout live)) ; eauto.
           eapply SSAvalidprop.use_code_spec; eauto.
           try solve [econstructor; eauto].
           unfold erase_reg. rewrite EQ. auto.
           erewrite H11 with (i:= p); eauto.
        -- exploit H11 ; eauto.
      * rewrite <- EQ.
        inv Hwtedge; allinv; well_typed.
        rewrite Bij.BIJ2; eauto.
        
    + intros [tf' [Hfind Htrans]].
      exists (Callstate (Stackframe dst tf sp pc' rs':: ts)  tf' rs'## args' m).
      split.
      DStep_tac.
      econstructor ; eauto with valagree.
      replace (rs'## args') with (rs##args).
      econstructor ; eauto. 
      replace args with (map (erase_reg size) args') in *.
      eapply wt_call_agree; eauto. 
      eapply check_args_spec_erased_rwt ; eauto.
      destruct ros; simpl in H0.
      { des_ifs.
        { (eapply Genv.find_funct_prop ; eauto). instantiate (1:= (Vptr b (Ptrofs.repr z))). ss. }
        { (eapply Genv.find_funct_prop ; eauto). instantiate (1:= (Vptr b i)). ss. } }
      { destruct Genv.find_symbol in H0 ; try congruence.
        (eapply Genv.find_funct_ptr_prop ; eauto). }
      
      inv Hwtedge; allinv ; well_typed ; inversion Hspec ; eapply agree_preserve_args ; eauto.
      intros ; eapply (wf_live_use f (Lout live)) ; eauto. 
      destruct ros ; eauto.
      intros ; eapply (wf_live_use f (Lout live)) ; eauto. 
      destruct ros ; eauto.  

  - (* tailcall *)
    exploit_hyps SPEC.
    exploit (Hwto pc). econstructor; eauto. clear Hwto; intros Hwto; inv Hwto; allinv.
    exploit (spec_ros_find_function size rs rs' fd ros fn') ;eauto.
    + intros. inv H4. inv H5. inv H7.
      destruct (Bij.rmap size r') as (rr',p) eqn:EQ.
      unfold erase_reg. rewrite EQ. simpl.
      replace r' with (Bij.pamr size (rr',p)).
      * well_typed.
        replace p with (Γ pc rr').
        eapply agree_preserve_arg; eauto ; conv.
        replace rr' with (erase_reg size r').
        eapply (wf_live_use f (Lout live)) ; eauto.
        eapply SSAvalidprop.use_code_spec; eauto.
        try solve [econstructor; eauto].
        unfold erase_reg; rewrite EQ. auto.
        erewrite H9; eauto.
        eapply H9; eauto.
      * rewrite <- EQ.
        well_typed.
        rewrite Bij.BIJ2; eauto.
    + intros [tf' [Hfind Htrans]].
      
      exists (Callstate ts tf' rs'## args' m').
      split. DStep_tac.  econstructor; eauto with valagree.
      congruence.
      
      replace (rs'## args') with (rs##args).
      econstructor; eauto.
      destruct ros; simpl in H0.
      { des_ifs.
        { (eapply Genv.find_funct_prop ; eauto). instantiate (1:= (Vptr b (Ptrofs.repr z))). ss. }
        { (eapply Genv.find_funct_prop ; eauto). instantiate (1:= (Vptr b i)). ss. } }
      { destruct Genv.find_symbol in H0 ; try congruence.
        (eapply Genv.find_funct_ptr_prop ; eauto). }
      (* (eapply Genv.find_funct_prop ; eauto). *)
      (* destruct Genv.find_symbol in H0 ; try congruence. *)
      (* (eapply Genv.find_funct_ptr_prop ; eauto).  *)
      
      well_typed; eapply agree_preserve_args; eauto. 
      intros ; eapply (wf_live_use f (Lout live)) ; eauto.
      destruct ros ; eauto.
      intros ; eapply (wf_live_use f (Lout live)) ; eauto.
      destruct ros ; eauto. 

  - (* built in *)
    unfold is_internal in INT. ss. des_ifs_safe. rename Heq into SRCINT.
    exists (State ts tf sp pc' (regmap_setres dst vres rs') m').
    split.
    + DStep_tac. eapply exec_Ibuiltin with (vargs:= vargs); eauto with valagree.
      * { exploit check_instr_spec_erase; eauto.
          simpl. intros [Heq _]. inv Heq.
          eapply agree_preserve_builtin_args; eauto with valagree.
          - intros ; eapply (wf_live_use f (Lout live)) ; eauto.
          - exploit (Hwte pc). econstructor; eauto.
            clear Hwte; intros Hwte; inv Hwte; allinv.
            inv WTI; eauto.
          - inv Hwtedge; allinv.
            inv WTI; eauto.
          - inv Hwtedge; allinv.
            inv WTI; eauto.
        }
      * eapply external_call_symbols_preserved; eauto with valagree.
        apply senv_preserved.
    + inv Hwtedge; allinv; well_typed.

      * matches pc pc'.
        eapply update_preserve_agree with (dst:= x0) (i:= i) ; eauto.
        -- unfold erase_reg. rewrite H12. auto.
        -- intros ; exploit (wf_live_incl f (Lout live)) ; eauto. 
           intuition. inversion H6 ; allinv. intuition.
        -- unfold erase_reg. rewrite H12. simpl. auto.
      * matches pc pc'.
        rewrite regmap_setres_erase_noBR; try solve [eapply H9 ; eauto].
        rewrite regmap_setres_noBR; try solve [eapply H9 ; eauto].
        unfold agree in * ; intros.
        exploit (wf_live_incl f (Lout live)) ; eauto. intros [Hok | Hcont].
        -- eapply (AG r) ; eauto.
        -- inv Hcont ; allinv.
           { destruct dst; simpl in *.
             - eelim H11 ; eauto.
             - congruence.
             - congruence.
           }
        -- auto.
        -- auto.
           
  - exploit_hyps SPEC.
    assert (Hedge : is_edge tf pc ifso) by (econstructor; eauto ; simpl ; auto).
    assert (Hwtedge : wt_edge tf _ (Lin f ifso (Lout live)) Γ pc ifso) by eauto.
    destruct b.
    
    + (* cond_true *)
      assert (exists i, (fn_code tf) ! ifso = Some i)
        by (eapply SSA.fn_code_closed; eauto). 
      destruct H1.
      
      exists (State ts tf sp ifso rs' m).
      split. DStep_tac. eapply exec_Icond_true ; eauto.
      replace (rs'## args') with (rs##args) ; eauto with valagree.
      eapply agree_preserve_args ; eauto.
      intros ; eapply (wf_live_use f (Lout live)) ; eauto.
      
      inv Hwtedge; allinv; try well_typed ; eauto.
      exploit (elim_structural tf WF pc ifso); eauto. congruence.
      { inv Hwtedge; allinv ; try inv WTI; eauto.
        error_struct tf pc ifso.
      }
      { inv Hwtedge; allinv ; try inv WTI; eauto.
        error_struct tf pc ifso.
      }      
      inv Hwtedge; allinv; try well_typed ; matches pc ifso.
      unfold agree in * ; intros.
      exploit (wf_live_incl f (Lout live)) ; eauto. intros [Hok | Hcont].
      eapply (AG r) ; eauto. inv Hcont ; allinv.
      error_struct tf pc ifso.
      
    + (* icond false *)
      clear Hedge Hwtedge.
      assert (Hedge : is_edge tf pc ifnot) by (econstructor; eauto; simpl; auto).
      assert (Hwtedge : wt_edge tf _ (Lin f ifnot (Lout live)) Γ pc ifnot) by eauto.

      assert (exists i, (fn_code tf) ! ifnot = Some i).
      eapply SSA.fn_code_closed; eauto. destruct H1.
      
      exists (State ts tf sp ifnot rs' m);
        split; try DStep_tac; try (eapply exec_Icond_false ; eauto).
      replace (rs'## args') with (rs##args) ; eauto with valagree.
      inv Hwtedge; allinv ; try well_typed ; eapply agree_preserve_args ; eauto.
      intros ; eapply (wf_live_use f (Lout live)) ; eauto.
      error_struct tf pc ifnot.
      error_struct tf pc ifnot.
      error_struct tf pc ifnot.
      error_struct tf pc ifnot.
      
      inv Hwtedge; allinv; try well_typed; matches pc ifnot.
      unfold agree in * ; intros.
      exploit (wf_live_incl f (Lout live) HWL pc ifnot) ; eauto. intros [Hok | Hcont].
      eapply (AG r) ; eauto. inv Hcont ; allinv.
      error_struct tf pc ifnot.
     
  - (* jump table *)
    exploit_hyps SPEC.
    assert (exists i, (fn_code tf) ! pc' = Some i).
    eapply SSA.fn_code_closed; eauto. simpl; auto.
    eapply list_nth_z_in; eauto. destruct H2.
    
    assert (Hedge : is_edge tf pc pc') by (econstructor; eauto; simpl; eapply list_nth_z_in; eauto).
    assert (Hwtedge : wt_edge tf _ (Lin f pc' (Lout live)) Γ pc pc') by auto.
    exists (State ts tf sp pc' rs' m);
      split; try DStep_tac; try (eapply exec_Ijumptable ; eauto).
    rewrite <- H0. symmetry.
    inv Hwtedge; allinv ; try well_typed; conv ; eauto with agree.
    + destruct (Bij.rmap size arg0) as (r, p) eqn:EQN.
      unfold erase_reg in * ; simpl fst in *. rewrite EQN. simpl.
      replace arg0 with (Bij.pamr size (r, p)).
      replace p with (Γ pc r).
      eapply agree_preserve_arg ; eauto.
      eapply (wf_live_use f (Lout live)) ; eauto.
      replace r with (erase_reg size arg0). 
      eapply SSAvalidprop.use_code_spec; eauto.
      try solve [econstructor; eauto].
      unfold erase_reg. rewrite EQN. auto.
      erewrite H7 ; eauto.
      exploit H7 ; eauto.
      rewrite <- EQN. rewrite Bij.BIJ2; eauto.

    + (exploit (elim_structural tf WF pc pc'); eauto).
      (eapply list_nth_z_in in H1; eauto).  
      congruence.
    + inv Hwtedge; allinv; try well_typed; matches pc pc'.
      unfold agree in * ; intros.
      exploit (wf_live_incl f (Lout live) HWL pc pc') ; eauto.
      econstructor ; eauto. 
      (eapply list_nth_z_in in H1; eauto).  
      intros [Hok | Hcont].
      eapply (AG r) ; eauto. inv Hcont ; allinv.
    
      (exploit (elim_structural tf WF pc pc'); eauto).
      (eapply list_nth_z_in in H1 ; eauto).
      congruence.

  - (* return None+Some *)
    exploit_hyps SPEC.
    exploit (Hwto pc). constructor 2 with (or:= None); eauto. clear Hwto; intros Hwto; inv Hwto; allinv.
    exists (SSA.Returnstate ts (regmap_optget None Vundef rs') m'); split ; eauto.
    DStep_tac.
    eapply SSA.exec_Ireturn; eauto. congruence.
    exploit (Hwto pc). constructor 2 with (or:= Some r); eauto. clear Hwto; intros Hwto; inv Hwto; allinv.
    exists (Returnstate ts (regmap_optget (Some r) Vundef rs') m'); split ; eauto.
    DStep_tac.
    eapply exec_Ireturn; eauto. congruence.
    simpl. replace (rs'#r) with (rs#(erase_reg size r)); eauto.
    well_typed; conv ; eauto with valagree. 
    destruct (Bij.rmap size r) as (rr, p) eqn:EQN.
    unfold erase_reg in * ; simpl fst in *. rewrite EQN. simpl.
    replace r with (Bij.pamr size (rr, p)).
    replace p with (Γ pc rr).
    eapply agree_preserve_arg ; eauto.
    eapply (wf_live_use f (Lout live)) ; eauto.
    replace rr with (erase_reg size r).
    eapply SSAvalidprop.use_code_spec; eauto.
    solve [econstructor; eauto].
    unfold erase_reg; rewrite EQN; simpl; auto.
    erewrite H3; eauto.
    exploit H3 ; eauto.
    rewrite <- EQN. rewrite Bij.BIJ2; eauto. 
    
  - (* internal *)
    simpl in TRANSF. monadInv TRANSF.   
    inv WFDFS ; auto.
    exploit WELL_TYPED; eauto.
    intros [live [TYPECHECK CFNS]].
    case_eq (extern_gen_ssa f (fun pc => Lin f pc (Lout live))) ; intros [size def] def_phi Hext.
    rewrite Hext in *.
    
    inv H1.
    exploit typecheck_function_correct; eauto.
    intros [Γ [WTF [WFINIT [HERA [HNORM [[HCK HNODUP] HH]]]]]].
    inv HERA. 

    exists (State ts x (Vptr stk Ptrofs.zero) x.(fn_entrypoint) (init_regs args x.(fn_params)) m').
    split.
    DStep_tac.
    eapply exec_function_internal; eauto.
    erewrite <- typecheck_function_correct_ssize; eauto.
    replace (RTLdfs.fn_entrypoint f) with (fn_entrypoint x) at 1; auto.
    replace (RTLdfs.fn_params f) with (map (erase_reg size) (fn_params x)); auto.
    
    econstructor ; eauto.
    * econstructor; eauto. 
      eapply typecheck_function_correct_structural_checks; eauto.
      econstructor; eauto.
    * eapply transf_function_wf_ssa_function; eauto.
      constructor; auto. 
    * eapply agree_init_regs_gamma ; eauto. 
      apply inclist_refl. 

  - (* external *)
    inv TRANSF.
    exists (Returnstate ts res m'). split.
    DStep_tac.
    eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto with valagree.
    eapply senv_preserved.
    econstructor ; eauto.

  - (* return state *)
    inv STACKS. 
    exists (State ts0 tf sp pc (rs'# res0 <- vres) m);
      split; try DStep_tac; ( try constructor ; eauto).
    
    econstructor ; eauto.
    unfold agree; intros.
    destruct (Bij.rmap size res0) as (r0,i) eqn:EQN.
    unfold erase_reg; rewrite EQN. simpl.
    destruct (peq r0 r).
    + (* same : receive the same value *)
      inv e. rewrite PMap.gss.
      unfold erase_reg, get_index in * ; rewrite EQN in *. simpl in H11. inv H11.
      rewrite <- EQN at 1. rewrite Bij.BIJ2; eauto.
      rewrite PMap.gss at 1 ; auto.
    + (* different : use the info in the stack *)
      rewrite PMap.gso ; auto.
      rewrite PMap.gso ; auto.
      * eapply H12; eauto.
        intro. subst.
        unfold erase_reg in *.  rewrite EQN in *.
        elim n. auto.
      * intro. subst. 
        unfold get_index, erase_reg in *. 
        rewrite EQN in *. simpl in *. subst.
        rewrite Bij.BIJ1 in EQN. inv EQN. congruence.
        auto.
Qed.

Lemma match_states_bsim
      s1 s2 s2' t
      (EXT: RTLdfs.is_external ge s1)
      (STEPTGT: Step tsem s2 t s2')
      (MATCH: s1 ≃ s2)
      (SAFESRC: safe sem s1)
  :
    (exists s1', Step sem s1 t s1' /\ s1' ≃ s2').
Proof.
  assert (SEQUIV: Senv.equiv tge ge) by (symmetry; apply senv_preserved).
  unfold safe in SAFESRC. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
  { inv SAFESRC. inv MATCH. inv STACKS. inv STEPTGT. }
  inv MATCH; ss; des_ifs; try (try exploit_hyps SPEC;
  try (assert (Hedge : is_edge tf pc n) by go;
    assert (Hwtedge : wt_edge tf _ (Lin f n (Lout live)) Γ pc n) by eauto);
  (exploit is_edge_pred ; eauto ; intros [x H2] ) ;
  try (
    assert (Hedge0 : is_edge tf pc0 pc) by (eapply pred_is_edge; eauto);
      assert (Hwtedge0 : wt_edge tf _ (Lin f n (Lout live)) Γ pc0 pc) by (eauto)
  );
  try (case_eq ((fn_phicode tf)!n); intros) ;
  try destruct (join_point_exclusive tf HWF n)); try (error n); try (error_struct tf pc n);
  try (instr_succ pc n Hi ; try (error n); try (error_struct tf pc n)).

  (* builtin *)
  - i. inv STEPTGT; clarify. inv SAFESRC; clarify.
    exists (RTLdfs.State s f sp n (regmap_setres (map_builtin_res (erase_reg size) dst) vres rs) m').
    esplits.
    + eapply RTLdfs.exec_Ibuiltin with (ef:=e) (args:=l).
      { eauto. }
      { instantiate (1:=vargs).
        exploit check_instr_spec_erase; eauto.
        simpl. intros [Heq _]. inv Heq.
        exploit eval_builtin_args_preserved; try eapply H15.
        { eapply senv_preserved. }
        i. exploit agree_preserve_builtin_args; try eapply H1; eauto with valagree.
        - intros ; eapply (wf_live_use f (Lout live)) ; eauto.
        - exploit (Hwte pc). econstructor; eauto.
          clear Hwte; intros Hwte; inv Hwte; allinv.
          inv WTI; eauto.
        - inv Hwtedge; allinv.
          inv WTI; eauto.
        - inv Hwtedge; allinv.
          inv WTI; eauto.
        - i. exploit eval_builtin_args_determ. eapply H12. eapply H3. i. subst.
          eauto. }
      eapply external_call_symbols_preserved; eauto.
    + inv Hwtedge; allinv; well_typed.

      * matches pc n.
        eapply update_preserve_agree with (dst:= x0) (i:= i) ; eauto.
        -- unfold erase_reg. rewrite H10. auto.
        -- intros ; exploit (wf_live_incl f (Lout live)) ; eauto. 
           intuition. inversion H5 ; allinv. intuition.
        -- unfold erase_reg. rewrite H10. simpl. auto.
      * matches pc n.
        rewrite regmap_setres_erase_noBR; try solve [eapply H9 ; eauto].
        rewrite regmap_setres_noBR; try solve [eapply H9 ; eauto].
        unfold agree in * ; intros.
        exploit (wf_live_incl f (Lout live)) ; eauto. intros [Hok | Hcont].
        -- eapply (AG r) ; eauto.
        -- inv Hcont ; allinv.
           { destruct dst; simpl in *.
             - eelim H9 ; eauto.
             - congruence.
             - congruence.
           }
  (* external call *)
  - i. inv STEPTGT; clarify. inv SAFESRC; clarify.
    inv TRANSF.
    exists (RTLdfs.Returnstate s res m'). split.
    eapply RTLdfs.exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto with valagree.
    econstructor ; eauto.
Qed.

Lemma match_states_xsim
    st_src0 st_tgt0 gmtgt
    (MATCH: match_states st_src0 st_tgt0) :
  xsim (RTLdfs.semantics prog) (semantics tprog) gmtgt lt 0%nat st_src0 st_tgt0.
Proof.
  generalize dependent st_src0. generalize dependent st_tgt0.
  pcofix CIH. i. pfold.
  destruct (classic (RTLdfs.is_external ge st_src0)); cycle 1.
  (* not external *)
  - left. econs. econs.
    + i. exploit transl_step_correct; eauto. i. des; esplits; eauto.
      { eapply tr_rel_refl. eapply ev_rel_refl. }
      left. split; eauto.
      { eapply plus_one; eauto. }
      { eapply RTLdfsD.semantics_receptive_at; auto. }
    + ii. eapply final_state_determ; eauto.
      inv FINALSRC. inv MATCH. ss. inv STACKS. econs.
  (* external *)
  - right. econs. i. econs.
    (* bsim *)
    + i. exploit match_states_bsim; eauto. i. des.
      left. esplits; eauto.
      { eapply tr_rel_refl. eapply ev_rel_refl. }
      left. eapply plus_one. eauto.
    + ii. inv FINALTGT. inv MATCH. inv STACKS. ss.
    (* progress *)
    + i. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
      { inv SAFESRC; ss. }
      right. inv MATCH; ss; des_ifs; inv SAFESRC; unfold ge in *; clarify; try (try exploit_hyps SPEC;
      try (assert (Hedge : is_edge tf pc n) by go;
           assert (Hwtedge : wt_edge tf _ (Lin f n (Lout live)) Γ pc n) by eauto);
          (exploit is_edge_pred ; eauto ; intros [x H2] ) ;
      try (assert (Hedge0 : is_edge tf pc0 pc) by (eapply pred_is_edge; eauto);
           assert (Hwtedge0 : wt_edge tf _ (Lin f n (Lout live)) Γ pc0 pc) by (eauto));
      try (case_eq ((fn_phicode tf)!n); intros) ;
      try destruct (join_point_exclusive tf HWF n)); try (error n); try (error_struct tf pc n);
      try (instr_succ pc n Hi ; try (error n); try (error_struct tf pc n)).
      * esplits. eapply exec_Ibuiltin. eauto.
        { instantiate (1:=vargs).
          exploit check_instr_spec_erase; eauto.
          simpl. intros [Heq _]. inv Heq.
          (* exploit eval_builtin_args_preserved; try eapply H15. *)
          (* { eapply senv_preserved. } *)
          (* i. *)
          exploit agree_preserve_builtin_args; eauto with valagree.
          - intros ; eapply (wf_live_use f (Lout live)) ; eauto.
          - exploit (Hwte pc). econstructor; eauto.
            clear Hwte; intros Hwte; inv Hwte; allinv.
            inv WTI; eauto.
          - inv Hwtedge; allinv.
            inv WTI; eauto.
          - inv Hwtedge; allinv.
            inv WTI; eauto. }
        eapply external_call_symbols_preserved; eauto with valagree.
        eapply senv_preserved.
      * inv TRANSF. esplits.
        eapply exec_function_external; eauto.
        eapply external_call_symbols_preserved; eauto with valagree.
        eapply senv_preserved.
Qed.

Lemma non_static_equiv l:
  Genv.non_static_glob (Genv.globalenv prog) l = Genv.non_static_glob (Genv.globalenv tprog) l.
Proof.
  induction l; ss.
  specialize senv_preserved. i. unfold ge, tge in H. r in H. des.
  specialize (H0 a).
  unfold Senv.public_symbol in H0. ss. rewrite <- H0.
  specialize (H a). rewrite <- H. erewrite IHl; eauto.
Qed.

Lemma transf_initial_capture
    S1 S2 S2'
    (INITSRC: RTLdfs.initial_state prog S1)
    (INITTGT: SSA.initial_state tprog S2)
    (MATCH: match_states S1 S2)
    (CAPTGT: SSA.glob_capture tprog S2 S2'):
  exists S1',
    RTLdfs.glob_capture prog S1 S1'
  /\ match_states S1' S2'
  /\ gm_improves (RTLdfs.concrete_snapshot ge S1') (SSA.concrete_snapshot tge S2').
Proof.
  specialize senv_preserved. intros SENVEQ. inv CAPTGT. ss.
  rewrite Genv.globalenv_public in CAPTURE.
  rewrite <- same_public in CAPTURE. erewrite <- non_static_equiv in CAPTURE.
  inv MATCH. inv STACKS.
  esplits.
  - econs; eauto. rewrite Genv.globalenv_public. eauto.
  - econs; eauto. econs.
  - ii. unfold RTLdfs.concrete_snapshot, SSA.concrete_snapshot in *.
    inv SENVEQ. des. erewrite H1, H0. des_ifs; ss.
Qed.

(** ** Final semantics preservation result *)
Theorem transf_program_correct:
  mixed_simulation (RTLdfs.semantics prog) (SSA.semantics tprog).
Proof.
  econs. econs.
  - apply lt_wf.
  - rr. i. exists (S a). lia.
  - econs. i. exploit transf_initial_states; eauto. i. des.
    exists st2. split.
    (* initial state *)
    + econs; eauto. eapply initial_state_determ.
    (* mixed sim *) 
    + r. ii. inversion INITSRC; subst. inversion H0; subst.
      inv STACKS.
      exploit transf_initial_capture; eauto.
      i. des.
      exists 0%nat. exists S1'. esplits; eauto.
      apply match_states_xsim; auto.
  - i. apply senv_preserved.
Qed.

End CORRECTNESS.

  
End PRESERVATION.
