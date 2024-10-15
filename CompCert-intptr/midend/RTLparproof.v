Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Globalenvs.
Require Import PointerOp Simulation CSSAD RTLparD sflib.
Require Import Smallstep.
Require Import Dom.
Require Import Op.
Require Import SSA.
Require Import SSAutils.
Require Import Utils.
Require Import CSSA.
Require RTLpar.
Require Import RTLpargen.
Require Import Kildall.
Require Import KildallComp.
Require Import DLib.
Require Import Events.
Require CSSAlive.
Require Import CSSAval.
Require Import CSSAninterf.
Require Import CSSAutils.
Require Import Classical.
Require Import CSSAdef.
Require Import Registers.
Require Import Classical.
From Paco Require Import paco.

Unset Allow StrictProp.

(*
  (pred)  u_k = a_k
          ...
          
  (pc)    u_0 = phi(...,u_k,...)
          ...

          a_0 = u_0
          ...

         use     def
  --------------------
  a_k    pred    <
  u_k    pred    pred
  u_0    pc      pc
  a_0    >=      pc

*)

Lemma compute_regrepr_correct :
  forall f r r' regrepr,
  wf_cssa_function f ->
  compute_regrepr f = Errors.OK regrepr ->
  regrepr r = regrepr r' ->
  (exists d1, def f r d1) ->
  (exists d2, def f r' d2) ->
  ninterfere_spec f r r'.
Proof.
  intros until regrepr. intro WF.
  intros Hcompute_regrepr Heq Hdefr Hdefr'.
  unfold compute_regrepr in Hcompute_regrepr.
  flatten Hcompute_regrepr.
  unfold check_coalescing_classes in Eq1.
  rewrite andb_true_iff in Eq1.
  destruct Eq1 as [Eq1 Hcssacoalescing].
  rewrite andb_true_iff in Eq1.
  destruct Eq1 as [Hforall Hmemext].
  rewrite andb_true_iff in Hforall.
  destruct Hforall as [Hforall Hmemregs].
  rewrite forallb_forall in Hforall.
  destruct Hdefr as [d1 Hdefr].
  destruct Hdefr' as [d2 Hdefr'].
  generalize compute_def_in_correct. 
  intros Hinlist.
  specialize (Hinlist f r d1).
  exploit Hinlist; eauto; intros.
  generalize compute_def_in_correct. 
  intros Hinlist2.
  specialize (Hinlist2 f r' d2).
  exploit Hinlist2; eauto; intros.
  assert(Wcssa: cssaval_spec f (compute_cssaval_function f)).
  {
    eapply check_cssaval_correct; auto.
    unfold compute_ninterfere in Eq.
    flatten Eq. rewrite negb_false_iff in Eq2; auto.
  }
  case_eq (peq r r'); intros Heqrr'.
  { rewrite Heqrr' in *. constructor; auto. }
  intros Heqrr'2.
  destruct H; destruct H0;
  match goal with
  | Hr: In r (map fst (PTree.elements (get_all_def f))),
    Hr': In r' (map fst (PTree.elements (get_all_def f)))
    |- _ =>
      generalize mem_class_regs_correct; intros Hclass1;
      specialize (Hclass1 regrepr t
        (map fst (PTree.elements (get_all_def f))) r);
      exploit Hclass1; eauto; intros Hexists_class1;
      generalize mem_class_regs_correct; intros Hclass2;
      specialize (Hclass2 regrepr t
        (map fst (PTree.elements (get_all_def f))) r');
      exploit Hclass2; eauto; intros Hexists_class2
  | Hr: In r (map fst (PTree.elements (get_all_def f))),
    Hr': SSARegSet.In r' (get_ext_params f (get_all_def f))
    |- _ =>
    generalize mem_class_regs_correct; intros Hclass1;
    specialize (Hclass1 regrepr t
      (map fst (PTree.elements (get_all_def f))) r);
    exploit Hclass1; eauto; intros Hexists_class1;
    generalize mem_class_regs_correct; intros Hclass2;
    specialize (Hclass2 regrepr t
      (SSARegSet.elements (get_ext_params f (get_all_def f)))
      r');
    exploit Hclass2; eauto;
    [ exploit SSARegSet.elements_1; eauto;
      intros Hin; apply InA_In; auto | intros Hexists_class2]
  | Hr: SSARegSet.In r (get_ext_params f (get_all_def f)),
    Hr': In r' (map fst (PTree.elements (get_all_def f)))
    |- _ =>
    generalize mem_class_regs_correct; intros Hclass1;
    specialize (Hclass1 regrepr t
      (map fst (PTree.elements (get_all_def f))) r');
    exploit Hclass1; eauto; intros Hexists_class1;
    generalize mem_class_regs_correct; intros Hclass2;
    specialize (Hclass2 regrepr t
      (SSARegSet.elements (get_ext_params f (get_all_def f)))
      r);
    exploit Hclass2; eauto;
    [ exploit SSARegSet.elements_1; eauto;
      intros Hin; apply InA_In; auto | intros Hexists_class2]
  | Hr: SSARegSet.In r (get_ext_params f (get_all_def f)),
    Hr': SSARegSet.In r' (get_ext_params f (get_all_def f))
    |- _ =>
    generalize mem_class_regs_correct; intros Hclass1;
    specialize (Hclass1 regrepr t
      (SSARegSet.elements (get_ext_params f (get_all_def f)))
      r');
    exploit Hclass1; eauto;
    [ exploit SSARegSet.elements_1; eauto;
      intros Hin; apply InA_In; auto | intros Hexists_class1];
    generalize mem_class_regs_correct; intros Hclass2;
    specialize (Hclass2 regrepr t
      (SSARegSet.elements (get_ext_params f (get_all_def f)))
      r);
    clear H0;
    exploit Hclass2; eauto;
    [ exploit SSARegSet.elements_1; eauto;
      intros Hin; apply InA_In; auto | intros Hexists_class2]
  | _ => idtac
  end;
  (destruct Hexists_class1 as [Hl1 | Hr1];
    destruct Hexists_class2 as [Hl2 | Hr2];
  [ destruct Hl1 as [cls Hl1]; destruct Hl1;
    destruct Hl2 as [cls0 Hl2]; destruct Hl2;
    assert(Hclass_eq: cls0 = cls) by congruence;
    rewrite Hclass_eq in *;
    assert(b r r' = true)
      by (eapply check_interference_in_class_correct; eauto;
      [ apply Hforall; eauto;
        assert(Hin: In (regrepr r, cls) (PTree.elements t))
         by (apply PTree.elements_correct; auto);
        eapply In_Insnd; eauto
      | intros; eapply ninterf_symmetric; eauto]);
    eapply compute_ninterfere_correct; eauto
  | rewrite Heq in *;
    destruct Hl1 as [cls Hl1]; destruct Hl1; destruct Hr2; congruence
  | rewrite Heq in *;
    destruct Hr1; destruct Hl2 as [cls Hl2]; destruct Hl2; congruence
  | rewrite Heq in *; destruct Hr1; destruct Hr2; congruence]).
Qed.

Lemma compute_regrepr_init :
  forall f regrepr phib pc r r' dst args,
  compute_regrepr f = Errors.OK regrepr ->
  (fn_phicode f) ! pc = Some phib ->
  In (Iphi args dst) phib ->
  In r (dst :: args) ->
  In r' (dst :: args) ->
  regrepr r = regrepr r'.
Proof.
  intros until args.
  intros Hregrepr Hphib Hphi Hinr Hinr'.
  unfold compute_regrepr in Hregrepr.
  flatten Hregrepr.
  rewrite andb_true_iff in Eq1.
  destruct Eq1 as [Hclasses Hcssaphis].
  unfold check_cssa_coalescing_in_phicode in Hcssaphis.
  unfold check_cssa_coalescing_in_phib in Hcssaphis.
  unfold check_phi_ressources_coalescing in Hcssaphis.
  rewrite forallb_forall in Hcssaphis.
  specialize (Hcssaphis phib).
  exploit Hcssaphis; eauto.
  exploit PTree.elements_correct; eauto. intros.
  eapply In_Insnd_phib; eauto.
  intros Hcssaphi.
  rewrite forallb_forall in Hcssaphi.
  specialize (Hcssaphi (Iphi args dst)).
  exploit Hcssaphi; eauto.
  intros Hcssaarg.
  rewrite forallb_forall in Hcssaarg.
  case_eq (peq r dst); intros;
  case_eq (peq r' dst); intros.
  congruence.
  exploit (Hcssaarg r'); eauto. inv Hinr'; auto. congruence.
  intros Eqr'dst. rewrite <- e in Eqr'dst.
  destruct peq in Eqr'dst; go.
  exploit (Hcssaarg r); eauto. inv Hinr; auto. congruence.
  intros Eqrdst. rewrite e.
  destruct peq in Eqrdst; go.
  exploit (Hcssaarg r'); eauto. inv Hinr'; auto. congruence.
  intros Eqr'dst.
  exploit (Hcssaarg r); eauto. inv Hinr; auto. congruence.
  intros Eqrdst.
  destruct peq in Eqr'dst; destruct peq in Eqrdst; go.
Qed.

(** ** Transformation spec *)
Variant transl_function_spec: CSSA.function -> RTLpar.function -> Prop :=
| transl_function_spec_intro:
    forall f tf regrepr
    (RegRepr: compute_regrepr f = Errors.OK regrepr)
    (codeNone: forall pc,
      (fn_code f) ! pc = None ->
      (RTLpar.fn_code tf) ! pc = None)
    (codeSome: forall pc ins,
      (fn_code f) ! pc = Some ins ->
      (RTLpar.fn_code tf) ! pc =
        Some (transl_instruction regrepr ins))
    (parcbNone: forall pc,
      (fn_parcopycode f) ! pc = None ->
      (RTLpar.fn_parcopycode tf) ! pc = None)
    (parcbSome: forall pc parcb,
      (fn_parcopycode f) ! pc = Some parcb ->
      (RTLpar.fn_parcopycode tf) ! pc =
        Some (parcb_cleanup (transl_parcb regrepr parcb))),
    transl_function_spec f tf.

Variant tr_function: CSSA.function -> RTLpar.function -> Prop :=
| tr_function_intro:
    forall f regrepr (Regrepr: compute_regrepr f = Errors.OK regrepr),
      tr_function
        f
        (RTLpar.mkfunction
        f.(fn_sig)
        (map regrepr f.(fn_params))
        f.(fn_stacksize)
        (transl_code regrepr f.(fn_code))
        (parcopycode_cleanup (transl_parcopycode regrepr f.(fn_parcopycode)))
        f.(fn_entrypoint)).

Lemma transl_function_charact:
  forall f tf,
  wf_cssa_function f ->
  transl_function f = Errors.OK tf ->
  tr_function f tf.
Proof.
  intros.
  unfold transl_function in H0.
  flatten H0.
  apply tr_function_intro. auto.
Qed.

Lemma transl_function_correct :
  forall f tf,
  tr_function f tf ->
  transl_function_spec f tf.
Proof.
  intros.
  inv H.
  apply transl_function_spec_intro with (regrepr := regrepr);
    auto; simpl; intros;
    try unfold transl_code;
    try unfold transl_parcopycode;
    try (rewrite PTree.gmap1; unfold option_map; flatten; go);
    try (unfold parcopycode_cleanup;
      rewrite PTree.gmap1; unfold option_map; flatten; go);
    try (rewrite PTree.gmap1 in Eq; unfold option_map in Eq;
      flatten Eq; go).
Qed.

Definition transl_fundef (f: CSSA.fundef) : res RTLpar.fundef :=
  transf_partial_fundef transl_function f.

(** match_states *)

(* Il va falloir plusieurs propriétés côté source.

   Il faut avoir la propriété qui dit que si deux
   variables ont même SSA valeur, alors si un point
   pc est atteint où elles sont toutes les deux vivantes,
   alors en ce point les regsets doivent matcher.

   Pour la liveness, il faudra utiliser que si une variable
   n'est pas vivante en un point, elle n'est pas utilisée
   en ce point.
*)

Variant lazydef (f : function) (r : reg) (pc : node) : Prop :=
| lazydef_phi:
    assigned_phi_spec (fn_phicode f) pc r ->
    lazydef f r pc
| lazydef_parcb':
    assigned_parcopy_spec (fn_parcopycode f) pc r ->
    join_point pc f ->
    lazydef f r pc.

Variant match_regset (f : CSSA.function) (pc : node) :
  SSA.regset -> SSA.regset -> Prop :=
| mrg_intro : forall rs rs' regrepr,
    forall (RegRepr: compute_regrepr f = Errors.OK regrepr),
      (forall r,  (cssalive_spec f r pc /\ ~ lazydef f r pc)
                  \/ lazydef f r pc ->
                  rs # r = rs' # (regrepr r)) ->
      match_regset f pc rs rs'.

Inductive match_stackframes : list CSSA.stackframe -> list RTLpar.stackframe -> Prop :=
| match_stackframes_nil: match_stackframes nil nil
| match_stackframes_cons:
    forall res f sp pc rs rs' s tf ts regrepr
      (STACK : match_stackframes s ts )
      (SPEC: transl_function f = Errors.OK tf)
      (WFF: wf_cssa_function f)
      (RegRepr: compute_regrepr f = Errors.OK regrepr)
      (MRs: forall r,
        (cssalive_spec f r pc /\ ~ lazydef f r pc /\ r <> res)
        \/ lazydef f r pc ->
        rs # r = rs' # (regrepr r))
      (Hnotlive: forall r,
        regrepr r = regrepr res ->
        r <> res ->
        ~ cssalive_spec f r pc)
      (Hnotlazydef: forall r, ~ lazydef f r pc),
    match_stackframes
      (Stackframe res f sp pc rs :: s)
      (RTLpar.Stackframe (regrepr res) tf sp pc rs' :: ts).

Global Hint Constructors match_stackframes: core.

Set Implicit Arguments.

Require Import Linking.

Section PRESERVATION.

  Definition match_prog (p: CSSA.program) (tp: RTLpar.program) :=
    match_program (fun cu f tf => transl_fundef f = Errors.OK tf) eq p tp.

  Lemma transf_program_match:
    forall p tp, transl_program p = OK tp -> match_prog p tp.
  Proof.
    intros. apply match_transform_partial_program; auto.
  Qed.

  Section CORRECTNESS.

    Variable prog: CSSA.program.
    Variable tprog: RTLpar.program.

    
    Let ge := Genv.globalenv prog.
    Let tge := Genv.globalenv tprog.

    Let sem := CSSA.semantics prog.
    Let tsem := RTLpar.semantics tprog.

    Hypothesis TRANSF_PROG: match_prog prog tprog.
    Hypothesis WF_PROG : wf_cssa_program prog.

    Variant match_states: CSSA.state -> RTLpar.state -> Prop :=
    | match_states_intro:
        forall s ts sp pc rs rs' m f tf
               (REACH: reachable prog (State s f sp pc rs m))
               (SPEC: transl_function f = Errors.OK tf)
               (STACK: match_stackframes s ts)
               (WFF: wf_cssa_function f)
               (MREG: match_regset f pc rs rs'),
          match_states
            (State s f sp pc rs m)
            (RTLpar.State ts tf sp pc rs' m)
    | match_states_call:
        forall s ts f tf args m
               (REACH: reachable prog (Callstate s f args m))
               (SPEC: transl_fundef f = Errors.OK tf)
               (STACK: match_stackframes s ts)
               (WFF: wf_cssa_fundef f),
          match_states
            (Callstate s f args m)
            (RTLpar.Callstate ts tf args m)
    | match_states_return:
        forall s ts v m
               (REACH: reachable prog (Returnstate s v m))
               (STACK: match_stackframes s ts ),
          match_states
            (Returnstate s v m)
            (RTLpar.Returnstate ts v m).
    Hint Constructors match_states: core.

    Variant match_init: CSSA.state -> RTLpar.state -> Prop :=
    | match_init_intro:
        forall s ts f tf args m
               (SPEC: transl_fundef f = Errors.OK tf)
               (STACK: match_stackframes s ts)
               (WFF: wf_cssa_fundef f),
          match_init
            (Callstate s f args m)
            (RTLpar.Callstate ts tf args m).

(* NOTE: important *)
Lemma parcb_transl_other :
  forall parcb f r rs' regrepr,
  compute_regrepr f = Errors.OK regrepr ->
  (forall src dst,
    In (Iparcopy src dst) parcb ->
    (regrepr r) <> (regrepr dst) \/
    regrepr r = regrepr dst /\
    rs' # (regrepr r) =
      rs' # (regrepr src)) ->
  (parcopy_store 
    (parcb_cleanup (transl_parcb regrepr parcb)) rs')
  # (regrepr r) =
    rs' # (regrepr r).
Proof.
  induction parcb; auto.
  intros f r rs' regrepr Hregrepr Hprops.
  simpl in *.
  destruct a.
  flatten; go.
  simpl.
  case_eq (peq (regrepr r)
    (regrepr r1)); intros.
  + rewrite e in *.
    rewrite PMap.gss; eauto.
    exploit (Hprops r0 r1). go.
    intros Hprop.
    destruct Hprop; go.
    destruct H0; go.
  + rewrite PMap.gso; eauto.
Qed.

(* NOTE: important *)
Lemma parcb_transl_store_in :
  forall parcb f rs' r src regrepr,
  In (Iparcopy src r) parcb ->
  NoDup (map parc_dst parcb) ->
  (forall src' dst,
    In (Iparcopy src' dst) parcb ->
    (regrepr r) <> (regrepr dst) \/
    rs' # (regrepr src') =
      rs' # (regrepr src)) ->
  compute_regrepr f = Errors.OK regrepr ->
  (parcopy_store 
    (parcb_cleanup (transl_parcb regrepr parcb)) rs')
    # (regrepr r) = rs' # (regrepr src).
Proof.
  induction parcb;
  intros f rs' r src regrepr Hin HNoDup Hprops Hregrepr;
  simpl in *.
  + contradiction.
  + destruct a.
    flatten; go.
    {
      destruct Hin.
      - assert (EQ1: r1 = r) by congruence.
        assert (EQ2: r0 = src) by congruence.
        rewrite EQ1, EQ2 in *.
        rewrite <- e.
        rewrite parcb_transl_other with (f := f); go; intros.
        case_eq(peq (regrepr src) (regrepr dst)); auto; intros.
        right.
        split; auto.
        exploit Hprops; go; intros.
        destruct H2; go.
      - inv HNoDup.
        eapply IHparcb; go.
    }
    destruct Hin.
    - assert (EQ1: r1 = r) by congruence.
      assert (EQ2: r0 = src) by congruence.
      rewrite EQ1, EQ2 in *.
      simpl.
      rewrite PMap.gss; auto.
    - inv HNoDup.
      case_eq (peq (regrepr r1) (regrepr r)); intros; simpl.
      { rewrite e in *.
        rewrite PMap.gss.
        exploit (Hprops r0 r1); auto; intros.
        destruct H1; congruence. }
      { rewrite PMap.gso; eauto. }
Qed.

(* 
   blocs de copies parallèles:
    - c'est la première occurence d'une copie qui l'emporte
    - dans cssa il n'y a qu'une seule définition, donc
      c'est facile
    - dans rtlpar, suite au coalescing, on peut avoir
      deux fois
        u = ...
        ...
        u = ...
      où le premier u provient de r1, et le deuxième de r2.
      celui qui l'emporte est le premier, mais si on a eu
      coalescing comme ça, c'est que les valeurs des trucs
      qu'on donne sont les mêmes, c'est à dire
        regrepr r1 = regrepr r2 = regrepr "trucs de droite".
*)

Lemma no_successive_jp :
  forall f pc pc',
  wf_cssa_function f ->
  join_point pc f ->
  join_point pc' f ->
  (fn_code f) ! pc = Some (Inop pc') ->
  False.
Proof.
  intros until pc'.
  intros WF jp_pc jp_pc' Hinop.
  induction WF.
  assert((fn_phicode f) ! pc = None).
  assert(HInpreds: In pc (get_preds f) !!! pc').
  apply make_predecessors_correct_1
    with (instr := Inop pc').
  auto. go.
  unfold successors_list in HInpreds.
  flatten HInpreds.
  apply fn_normalized_jp with (pc := pc')
    (preds := (get_preds f) !!! pc'); try congruence.
  apply fn_phicode_inv; auto.
  unfold successors_list. flatten.
  unfold successors_list. flatten.
  auto.
  inv HInpreds.
  assert((fn_phicode f) ! pc <> None).
  apply fn_phicode_inv; auto.
  congruence.
Qed.

(** ** Simulation lemmas *)
Lemma not_lazydef_in_pred :
  forall f pc pc' phib r,
  wf_cssa_function f ->
  (fn_phicode f) ! pc' = Some phib ->
  (fn_code f) ! pc = Some (Inop pc') ->
  ~ lazydef f r pc.
Proof.
  intros until r.
  intros WF Hphib Hinop.
  unfold not; intros Hlazy.
  assert ((fn_phicode f) ! pc = None).
  eapply jp_not_preceded_by_jp; eauto. go.
  inv Hlazy.
  inv H0. go.
  inv H0.
  induction WF.
  assert ((fn_phicode f) ! pc <> None).
  apply fn_phicode_inv; auto.
  congruence.
Qed.

Lemma not_use_and_def_in_jppred :
  forall f pc parcb pc' phib r src,
  wf_cssa_function f ->
  (fn_parcopycode f) ! pc = Some parcb ->
  (fn_phicode f) ! pc' = Some phib ->
  (fn_code f) ! pc = Some (Inop pc') ->
  In (Iparcopy src r) parcb ->
  ~ def f src pc.
Proof.
  intros until src.
  intros WF Hparcb Hphib Hinop HIn.
  unfold not; intros.
  inv H.
  + assert ((fn_parcopycode f) ! (fn_entrypoint f) = None).
    induction WF; go. congruence.
  + inv H0; go.
  + inv H0.
    assert(WFaux: wf_cssa_function f) by auto.
    induction WF.
    assert(Hjp: join_point pc f).
    apply fn_phicode_inv.
    congruence.
    apply no_successive_jp with (f := f) (pc := pc) (pc' := pc').
    auto. auto.
    apply fn_phicode_inv. congruence.
    auto.
  + assert (use_parcopycode f src pc).
    go.
    induction WF.
    assert (~ assigned_parcopy_spec (fn_parcopycode f) pc src).
    go. congruence.
Qed.

Ltac eqregreprs regrepr0 regrepr :=
    assert(EQREGREPRS: regrepr0 = regrepr) by congruence;
    rewrite EQREGREPRS in *.

(* Simulation of parcopyblock in predecessor of joinpoint *)
Lemma simul_parcb :
  forall r f parcb' phib parcb
    rs rs' regrepr pc pc' s sp d m,
  wf_cssa_function f ->
  check_cssaval f (compute_cssaval_function f)
    (get_ext_params f (get_all_def f)) = true ->
  reachable prog (State s f sp pc rs m) -> 
  compute_regrepr f = Errors.OK regrepr ->
  (fn_phicode f) ! pc'     = Some phib ->
  (fn_code f) ! pc         = Some (Inop pc') ->
  (fn_parcopycode f) ! pc  = Some parcb ->
  (fn_parcopycode f) ! pc' = Some parcb' ->
  match_regset f pc rs rs' ->
  def f r d ->
  (cssalive_spec f r pc' /\
      ~ assigned_parcopy_spec (fn_parcopycode f) pc r)
    \/ assigned_parcopy_spec (fn_parcopycode f) pc r ->
  (parcopy_store parcb rs) !! r =
    (parcopy_store (parcb_cleanup (transl_parcb regrepr parcb)) rs')
      !! (regrepr r).
Proof.
  intros until m.
  intros WF Wcssaval Reach Regrepr Hphib Hinop
    Hparcb Hparcb' MR HDEF H.
  destruct H.
  + destruct H.
    rewrite parcb_other; go.
    assert (Hlive: cssalive_spec f r pc).
    {
      constructor 2 with (pc' := pc'); go.
      unfold not; intros.
      inv H1; auto.
      induction WF; go.
      inv H2; congruence.
      inv H2.
      induction WF.
      destruct H3 as [args HIn].
      assert(join_point pc f).
      apply fn_phicode_inv; congruence.
      assert(join_point pc' f).
      apply fn_phicode_inv; congruence.
      apply no_successive_jp
        with (f := f) (pc := pc) (pc' := pc'); eauto.
      constructor; eauto.
    }
    assert(Hdotranslparcb:
      (parcopy_store (parcb_cleanup (transl_parcb regrepr parcb)) rs')
        !! (regrepr r)
      = rs' !! (regrepr r)).
    {
      apply parcb_transl_other with (f := f); auto; intros.
      case_eq (peq (regrepr r) (regrepr dst));
        auto; intros.
      rewrite <- e in *. right.
      exploit compute_regrepr_correct; eauto.
      { exists pc. go. }
      intros Hninterf.
      assert (Hnotlivesrc: cssalive_spec f src pc).
      constructor; go.
      {
        unfold not; intros.
        assert(use_parcopycode f src pc) by go.
        inv H3.
        induction WF; go.
        inv H5; go.
        inv H5; go.
        assert ((fn_phicode f) ! pc = None).
        eapply jp_not_preceded_by_jp; go.
        congruence.
        induction WF.
        assert (~ assigned_parcopy_spec (fn_parcopycode f) pc src).
        go. go.
      }
      inv Hninterf.
      exploit (cssaval_transfer_in_parcopy src dst); eauto; intros.
      assert(compute_cssaval_function f r
        = compute_cssaval_function f src) by congruence.
      assert(rs !! r = rs !! src).
      eapply cssaval_spec_correct_2; eauto;
      match goal with
      | |- cssadom f ?src pc =>
          assert(Hdomentry: cssadom f src pc \/ (pc = fn_entrypoint f))
             by (apply CSSAlive.live_cssadom; auto;
              eapply fn_code_reached; eauto);
            inv Hdomentry; auto;
            assert((fn_parcopycode f) ! (fn_entrypoint f) = None)
             by (eapply fn_no_parcb_at_entry; eauto);
            try congruence
      | _ => idtac
      end.
      unfold cssaval; flatten.
      inv MR.
      eqregreprs regrepr0 regrepr.
      rewrite <- H8.
      rewrite <- H8.
      auto.
      left. split.  auto.
      eapply not_lazydef_in_pred; eauto.
      left. split. auto.
      eapply not_lazydef_in_pred; eauto.
      inv H3.
      assert (Hdefdst: def f dst pc) by go.
      assert (Eq: d2 = pc).
      eapply def_def_eq; eauto.
      rewrite Eq in *.
      assert (cssaliveout_spec f r pc).
      apply correspondance_outin with pc'; go.
      congruence.
    }
    rewrite Hdotranslparcb.
    inv MR; go.
    eqregreprs regrepr0 regrepr.
    apply H1.
    left. split.
    go.
    eapply not_lazydef_in_pred; eauto.
    (* not assigned *)
    intros.
    unfold not in *; intros.
    apply H0; go.
  + inv H.
    assert (Heqparcbs: parcb0 = parcb).
    congruence. rewrite Heqparcbs in *.
    destruct H1 as [src Hin].
    rewrite parcb_store_in with (src := src); eauto.
    rewrite parcb_transl_store_in with (f := f) (src := src); eauto.
    inv MR.
    eqregreprs regrepr0 regrepr.
    apply H.
    assert (Hnotlivesrc: cssalive_spec f src pc).
    constructor; go.
    eapply not_use_and_def_in_jppred; eauto.
    left; split; go.
    eapply not_lazydef_in_pred; eauto.
    eapply nodup_in_parcb_dst; eauto.
    {
      intros.
      case_eq (peq (regrepr r) (regrepr dst)); auto; intros.
      right.
      exploit compute_regrepr_correct; eauto.
      { exists pc. go. }
      intros Hninterf.
      assert (Hnotlivesrc: cssalive_spec f src pc).
      constructor; go.
      eapply not_use_and_def_in_jppred; eauto.
      assert (Hnotlivesrc': cssalive_spec f src' pc).
      constructor; go.
      eapply not_use_and_def_in_jppred; eauto.
      inv Hninterf.
      exploit (cssaval_transfer_in_parcopy src' dst); eauto; intros.
      exploit (cssaval_transfer_in_parcopy src r); eauto; intros.
      assert (compute_cssaval_function f src'
        = compute_cssaval_function f src) by congruence.
      assert (Heq: rs !! src' = rs !! src).
      eapply cssaval_spec_correct_2; eauto;
      match goal with
      | |- cssadom f ?src pc =>
          assert(Hdomentry: cssadom f src pc \/ (pc = fn_entrypoint f))
             by (apply CSSAlive.live_cssadom; auto;
              eapply fn_code_reached; eauto);
            inv Hdomentry; auto;
            assert((fn_parcopycode f) ! (fn_entrypoint f) = None)
             by (eapply fn_no_parcb_at_entry; eauto);
            try congruence
      | _ => idtac
      end.
      unfold cssaval; flatten.
      inv MR.
      eqregreprs regrepr0 regrepr.
      rewrite <- H7.
      rewrite <- H7.
      go.
      left. split; auto.
      eapply not_lazydef_in_pred; eauto.
      left. split; auto.
      eapply not_lazydef_in_pred; eauto.
      go.
      inv H2.
      assert (Hdefdst: def f dst pc) by go.
      assert (Eq: d2 = pc).
      eapply def_def_eq; eauto.
      assert (Eq2: d1 = pc).
      eapply def_def_eq; eauto.
      go.
      congruence.
    }
    eapply nodup_in_parcb_dst; eauto.
Qed.

(* Simulation of parcopyblock and phiblock *)
Lemma simul_parcbphib :
  forall r f parcb' phib k parcb
    rs rs' regrepr pc pc' s sp d m,
  wf_cssa_function f ->
  check_cssaval f (compute_cssaval_function f)
    (get_ext_params f (get_all_def f)) = true ->
  reachable prog (State s f sp pc rs m) -> 
  compute_regrepr f = Errors.OK regrepr ->
  (fn_phicode f) ! pc'     = Some phib ->
  (fn_code f) ! pc         = Some (Inop pc') ->
  (fn_parcopycode f) ! pc  = Some parcb ->
  (fn_parcopycode f) ! pc' = Some parcb' ->
  index_pred (get_preds f) pc pc' = Some k ->
  (cssalive_spec f r pc' /\
      ~ assigned_parcopy_spec (fn_parcopycode f) pc r /\
      ~ assigned_phi_spec (fn_phicode f) pc' r)
    \/ assigned_parcopy_spec (fn_parcopycode f) pc r
    \/ assigned_phi_spec (fn_phicode f) pc' r ->
  match_regset f pc rs rs' ->
  def f r d ->
  (phi_store k phib
    (parcopy_store parcb rs)) !! r =
  (parcopy_store (parcb_cleanup (transl_parcb regrepr parcb)) rs') !! (regrepr r).
Proof.
  intros until m.
  intros WF Wcssaval Reach Hregrepr Hphib Hinop Hparcb Hparcb' Hindex
    Hprops MR Hdef.
  case_eq (In_dst_phib r phib);
    intros.
  + (* r in phib *)
    exploit In_dst_phib_true; eauto; intros.
    destruct H0 as [args Hin].
    assert (Harg: exists arg, nth_error args k = Some arg).
    eapply fn_phiargs; eauto.
    destruct Harg as [arg Hnth].
    assert (regrepr arg = regrepr r).
    {
      eapply compute_regrepr_init; eauto.
      induction WF; auto.
      constructor 2.
      eapply nth_error_in; eauto.
    }
    rewrite <- H0. 
    erewrite phi_store_in; eauto.
    assert(USE: use f arg pc) by go.
    exploit exists_def; eauto; intros DEF;
      destruct DEF as [argdef DEF].
    eapply simul_parcb; eauto.
    {
      (* NOTE: use of CSSA extension *)
      induction WF. right; auto.
      exploit fn_jp_use_phib; go.
    }
  + (* r not in phib *)
    assert (Hnotin: forall args, ~ In (Iphi args r) phib).
    apply In_dst_phib_false; auto.
    rewrite <- phi_store_other.
    eapply simul_parcb; go.
    destruct Hprops as [Hprops | Hprops].
    left. destruct Hprops as [MR1 [MR2 MR3]]. split; go.
    right. destruct Hprops. auto.
    inv H0. destruct H2 as [args Hin].
    assert(EQ: phiinstr = phib) by congruence.
    rewrite EQ in *.
    assert(Hnotinphib: ~ In (Iphi args r) phib).
    apply In_dst_phib_false; auto.
    congruence.
    intros. unfold not; intros.
    assert (~ In (Iphi args dst) phib).
    rewrite H1 in *. apply Hnotin.
    auto.
Qed.

Lemma liveinout_jp :
  forall f pc r,
  wf_cssa_function f ->
  join_point pc f ->
  cssalive_spec f r pc ->
  cssaliveout_spec f r pc.
Proof.
  intros f pc r WF Hjp Hlive.
  assert (exists succ, (fn_code f) ! pc = Some (Inop succ)).
  {
    induction WF. apply fn_inop_in_jp.
    rewrite fn_phicode_inv in Hjp. auto.
  }
  destruct H as [succ Hinop].
  inv Hlive.
  inv H0.
  + inv H1; go.
  + assert(join_point succ f).
    inv H1.
    assert(is_edge (fn_code f) pc pc0).
    eapply pred_is_edge_help; eauto.
    inv H0.
    assert(EQ: instr = Inop succ) by congruence.
    rewrite EQ in *.
    simpl in *.
    destruct H2; try contradiction.
    rewrite <- H0 in *.
    induction WF; apply fn_phicode_inv; congruence.
    induction WF; intuition.
  + induction WF.
    intuition.
  + eapply correspondance_outin; eauto.
  + eapply correspondance_outin; eauto.
Qed.

Lemma invariant_props_used_in_parcb' :
  forall f pc pc' phib parcb' src r,
  wf_cssa_function f ->
  (fn_code f) ! pc = Some (Inop pc') ->
  (fn_phicode f) ! pc' = Some phib ->
  (fn_parcopycode f) ! pc' = Some parcb' ->
  In (Iparcopy src r) parcb' -> 
  cssalive_spec f src pc' /\
  ~ assigned_parcopy_spec (fn_parcopycode f) pc src /\
  ~ assigned_phi_spec (fn_phicode f) pc' src \/
  assigned_parcopy_spec (fn_parcopycode f) pc src \/
  assigned_phi_spec (fn_phicode f) pc' src.
Proof.
  intros until r.
  intros WF Hinop Hphib Hparcb' Hin.
  right. right.
  induction WF.
  (* NOTE: use of CSSA extension *)
  apply fn_jp_use_parcb'.
  apply fn_phicode_inv.
  congruence. go.
Qed.

Lemma cssaval_props_used_in_parcb' :
  forall f pc pc' phib parcb' src r,
  wf_cssa_function f ->
  (fn_code f) ! pc = Some (Inop pc') ->
  (fn_phicode f) ! pc' = Some phib ->
  (fn_parcopycode f) ! pc' = Some parcb' ->
  In (Iparcopy src r) parcb' -> 
  cssadom f src pc /\
  ~ assigned_phi_spec (fn_phicode f) pc' src /\
  ~ assigned_parcopy_spec (fn_parcopycode f) pc src /\
  ~ assigned_parcopy_spec (fn_parcopycode f) pc' src \/
  assigned_parcopy_spec (fn_parcopycode f) pc src \/
  assigned_phi_spec (fn_phicode f) pc' src.
Proof.
  intros until r.
  intros WF Hinop Hphib Hparcb' Hin.
  right. right.
  induction WF.
  (* NOTE: use of CSSA extension *)
  apply fn_jp_use_parcb'.
  apply fn_phicode_inv.
  congruence. go.
Qed.

Ltac do_not_jp_pred pc_2 pc'_2 :=
    eapply no_successive_jp with (pc := pc_2) (pc' := pc'_2); eauto;
      rewrite fn_phicode_inv; try congruence.

Lemma rewrite_with_cssaval_until_jp :
  forall f pc' phib pc parcb parcb'
    src r k rs s sp m,
  wf_cssa_function f ->
  reachable prog (State s f sp pc rs m) -> 
  check_cssaval f (compute_cssaval_function f)
    (get_ext_params f (get_all_def f)) = true ->
  (fn_phicode f) ! pc' = Some phib ->
  (fn_code f) ! pc = Some (Inop pc') ->
  (fn_parcopycode f) ! pc = Some parcb ->
  (fn_parcopycode f) ! pc' = Some parcb' ->
  In (Iparcopy src r) parcb' ->
  index_pred (get_preds f) pc pc' = Some k ->
  cssaval_spec f (compute_cssaval_function f) ->
  (phi_store k phib (parcopy_store parcb rs)) !! src =
  (phi_store k phib (parcopy_store parcb rs))
  !! (compute_cssaval_function f src).
Proof.
  intros.
  assert(Hinoppc':
    exists pc'', (fn_code f) ! pc' = Some (Inop pc''))
    by (apply fn_inop_in_jp; try congruence);
  destruct Hinoppc' as [pc'' Hinoppc'].
  apply cssaval_spec_jp_until_phi
    with (f := f) (pc := pc) (pc' := pc') (parcb' := parcb')
      (get_cssaval := compute_cssaval_function f)
      (pc'' := pc''); auto.
  eapply fn_code_reached; eauto.
  apply fn_phicode_inv; try congruence.
  intros; unfold not; intros Hassignphi; inv Hassignphi.
  do_not_jp_pred pc pc'.
  unfold not; intros.
  do_not_jp_pred pc pc'.
  intros.
  exploit cssaval_spec_correct; eauto.
  { intros Hcssaval. unfold cssaval in *. flatten Hcssaval. }
  constructor 2. 
  { apply fn_jp_use_parcb'; auto. (* NOTE: extra CSSA invariants *)
    apply fn_phicode_inv; try congruence. go. }
  eapply cssaval_props_used_in_parcb'; eauto.
Qed.

(* Simulation of chain parcb-phib-parcb' *)
Lemma simul_parcbphibparcb' :
  forall r f parcb' phib k parcb
    rs rs' regrepr pc pc' s sp d m,
  wf_cssa_function f ->
  check_cssaval f (compute_cssaval_function f)
    (get_ext_params f (get_all_def f)) = true ->
  reachable prog (State s f sp pc rs m) -> 
  compute_regrepr f = Errors.OK regrepr ->
  (fn_phicode f) ! pc'     = Some phib ->
  (fn_code f) ! pc         = Some (Inop pc') ->
  (fn_parcopycode f) ! pc  = Some parcb ->
  (fn_parcopycode f) ! pc' = Some parcb' ->
  index_pred (get_preds f) pc pc' = Some k ->
  match_regset f pc rs rs' ->
  ((cssalive_spec f r pc' /\ ~ lazydef f r pc'
      /\ ~ assigned_parcopy_spec (fn_parcopycode f) pc r)
    \/
    (cssalive_spec f r pc' /\ ~ lazydef f r pc'
      /\ assigned_parcopy_spec (fn_parcopycode f) pc r)
    \/ lazydef f r pc') ->
  def f r d ->
  (parcopy_store parcb'
    (phi_store k phib
      (parcopy_store parcb rs)))
  !! r =
  (parcopy_store (parcb_cleanup (transl_parcb regrepr parcb'))
    (parcopy_store (parcb_cleanup (transl_parcb regrepr parcb))
      rs'))
  !! (regrepr r).
Proof.
  intros until m.
  intros WF Wcssaval Reach Hregrepr Hphib Hinop Hparcb Hparcb' Hindex
    MR Hprops Hdef.
  case_eq (In_dst_parcb r parcb');
    intros.
  + (* r is in parcb' *)
    exploit In_dst_parcb_true; eauto; intros.
    destruct H0 as [src Hin].
    assert(USE: use f src pc') by go.
    exploit exists_def; eauto; intros DEF;
      destruct DEF as [srcdef DEF].
    rewrite parcb_store_in with (src := src); eauto.
    rewrite parcb_transl_store_in with (f := f) (src := src); eauto.
    eapply simul_parcbphib; go.
    eapply invariant_props_used_in_parcb'; eauto.
    eapply nodup_in_parcb_dst; eauto.
    {
      intros.
      assert(USE': use f src' pc') by go.
      exploit exists_def; eauto; intros DEF';
      destruct DEF' as [src'def DEF'].
      case_eq (peq (regrepr r) (regrepr dst)); auto; intros.
      right.
      exploit compute_regrepr_correct; go.
      intros Hninterf.
      inv Hninterf.
      exploit (cssaval_transfer_in_parcopy src' dst); eauto; intros.
      exploit (cssaval_transfer_in_parcopy src r); eauto; intros.
      assert (compute_cssaval_function f src'
        = compute_cssaval_function f src) by congruence.
      erewrite <- simul_parcbphib; eauto.
      erewrite <- simul_parcbphib; eauto.
      {
        erewrite rewrite_with_cssaval_until_jp; eauto. symmetry.
        erewrite rewrite_with_cssaval_until_jp; eauto. go.
      }
      eapply invariant_props_used_in_parcb'; eauto.
      eapply invariant_props_used_in_parcb'; eauto.
      inv H2.
      assert (Eq: d2 = pc').
      eapply def_def_eq; go.
      assert (Eq2: d1 = pc').
      eapply def_def_eq; go.
      congruence.
    }
    eapply nodup_in_parcb_dst; eauto.
  + (* r is not in parcb' *)
    assert (Hnotin: forall src, ~ In (Iparcopy src r) parcb').
    apply In_dst_parcb_false; auto.
    assert(Hassigned_r:
      cssalive_spec f r pc' /\
      ~ assigned_parcopy_spec (fn_parcopycode f) pc r /\
      ~ assigned_parcopy_spec (fn_parcopycode f) pc' r /\
      ~ assigned_phi_spec (fn_phicode f) pc' r \/
      assigned_parcopy_spec (fn_parcopycode f) pc r \/
      assigned_phi_spec (fn_phicode f) pc' r).
    {
        decompose [or] Hprops.
        decompose [and] H0.
        left. repeat split; go.
        unfold not; intros. assert (lazydef f r pc').
        constructor 2; auto. rewrite fn_phicode_inv; go. contradiction.
        unfold not; intros. assert (lazydef f r pc').
        go. congruence.
        decompose [and] H1.
        right. left. auto.
        assert (~ assigned_parcopy_spec (fn_parcopycode f) pc' r).
        unfold not; intros.
        inv H0. destruct H3.
        replace parcb0 with parcb' in *.
        assert (~ In (Iparcopy x r) parcb').
        apply In_dst_parcb_false; auto. congruence. go.
        right. right.
        inv H1; go.
    }
    case_eq (In_dst_parcb (regrepr r)
      (parcb_cleanup (transl_parcb regrepr parcb')));
      intros.
    - (* [regrepr r] in transl(parcb') *)
      assert (Hintransl: exists src, In (Iparcopy src (regrepr r)) 
        (parcb_cleanup (transl_parcb regrepr parcb'))).
      apply In_dst_parcb_true; auto.
      destruct Hintransl as [src Hintransl].
      rewrite parcb_transl_other with (f := f); go.
      rewrite parcb_other; go.
      eapply simul_parcbphib; eauto.
        tauto.
      unfold not in *; intros.
      eapply Hnotin; go.
      {
        intros.
        assert(USE0: use f src0 pc') by go.
        exploit exists_def; eauto; intros DEF0;
        destruct DEF0 as [src0def DEF0].
        case_eq (peq (regrepr r) (regrepr dst)); auto; intros.
        right.
        exploit compute_regrepr_correct; go.
        intros Hninterf.
        inv Hninterf.
        exploit (cssaval_transfer_in_parcopy src0 dst); eauto; intros.
        assert (compute_cssaval_function f r
          = compute_cssaval_function f src0) by congruence.
        erewrite <- simul_parcbphib; eauto.
        erewrite <- simul_parcbphib; eauto.
        {
          split; auto.
          symmetry; erewrite rewrite_with_cssaval_until_jp; eauto;
            symmetry.
          assert(Hinoppc':
            exists pc'', (fn_code f) ! pc' = Some (Inop pc''))
            by (apply fn_inop_in_jp; try congruence);
          destruct Hinoppc' as [pc'' Hinoppc'].
          rewrite cssaval_spec_jp_until_phi
            with (f := f) (pc := pc) (pc' := pc') (parcb' := parcb')
              (get_cssaval := compute_cssaval_function f)
              (pc'' := pc''); auto.
          go.
          eapply fn_code_reached; eauto.
          apply fn_phicode_inv; try congruence.
          intros; unfold not; intros Hassignphi; inv Hassignphi.
          do_not_jp_pred pc pc'.
          unfold not; intros.
          do_not_jp_pred pc pc'.
          intros.
          exploit cssaval_spec_correct; eauto.
          { intros Hcssaval. unfold cssaval in *. flatten Hcssaval. }
          {
            decompose [or] Hassigned_r.
            assert(Hdomentry: cssadom f r pc' \/
                (pc' = fn_entrypoint f)).
              apply CSSAlive.live_cssadom; auto.
              tauto.
              eapply fn_code_reached; eauto.
              inv Hdomentry. auto.
              assert((fn_parcopycode f) ! (fn_entrypoint f) = None)
               by (eapply fn_no_parcb_at_entry; eauto).
              congruence.
            {
              inv Hprops; auto.
              tauto.
              destruct H7.
              destruct H7.
              exploit CSSAlive.live_cssadom; eauto.
              eapply fn_code_reached; eauto.
              intros. inv H10; auto.
              assert(Hcfg: cfg f pc (fn_entrypoint f)). go.
              contradict Hcfg.
              apply fn_entry_pred; eauto.
              inv H7. constructor 2; auto.
              constructor 3; auto.
            }
            constructor 2; auto.
          }
          decompose [or] Hassigned_r.
          {
            assert(cssalive_spec f r pc).
            constructor 2 with (pc' := pc'). go.
            unfold not; intros Hdefr.
            decompose [and] H7.
            inv Hdefr; go.
            assert ((fn_parcopycode f) ! (fn_entrypoint f) = None).
            induction WF; go. congruence.
            inv H11; go.
            inv H11.
            do_not_jp_pred pc pc'.
            tauto.
            left.
            split; auto.
            { assert(Hdomentry: cssadom f r pc \/
                (pc = fn_entrypoint f)).
              apply CSSAlive.live_cssadom; auto.
              eapply fn_code_reached; eauto.
              inv Hdomentry. auto.
              assert((fn_parcopycode f) ! (fn_entrypoint f) = None)
               by (eapply fn_no_parcb_at_entry; eauto).
              congruence. }
            repeat split; try tauto.
          }
          go. go.
        }
        eapply invariant_props_used_in_parcb'; eauto.
        tauto.
        inv H3.
        assert(Hdefdst: def f dst pc'). constructor 4; go.
        assert(EQ: d2 = pc').
        eapply def_def_eq; go.
        rewrite EQ in *.
        assert (cssalive_spec f r pc').
        { 
          decompose [or] Hprops; go.
          decompose [and] H3; go.
          decompose [and] H9; go.
          assert(def f r pc').
          inv H9; go.
          assert(d1 = pc').
          eapply def_def_eq; go. congruence.
        }
        assert (cssaliveout_spec f r pc').
        apply liveinout_jp; auto.
        induction WF. apply fn_phicode_inv. congruence.
        congruence.
      }
    - (* [regrepr r] not in transl(parcb') *)
      rewrite parcb_other.
      rewrite parcb_other.
      eapply simul_parcbphib; eauto.
      tauto.
      intros.
      assert (Hnotintransl: forall src,
        ~ In (Iparcopy src (regrepr r))
        (parcb_cleanup (transl_parcb regrepr parcb'))).
      apply In_dst_parcb_false; auto.
      unfold not in *; intros.
      eapply Hnotintransl; go.
      unfold not in *; intros.
      eapply Hnotin; go.
Qed.

(* Misc lemmas *)
Lemma registers_equal :
  forall args (rs rs' : SSA.regset) regrepr,
  (forall r, In r args ->
    rs !! r = rs' !! (regrepr r)) ->
  rs ## args = rs' ## (map regrepr args).
Proof.
  induction args; intros.
  go.
  simpl.
  rewrite <- IHargs with (rs := rs).
  rewrite H. auto. constructor; auto.
  intros. auto.
Qed.

Lemma stacksize_preserved:
  forall f tf,
  transl_function f = Errors.OK tf ->
  fn_stacksize f = RTLpar.fn_stacksize tf.
Proof.
  intros.
  unfold transl_function in H.
  flatten H; go.
Qed.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  eapply Genv.find_symbol_transf_partial ; eauto. 
Qed.

Lemma function_ptr_translated:
  forall (b: Values.block) (f: CSSA.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf
    /\ transl_fundef f = Errors.OK tf.
Proof.
  eapply Genv.find_funct_ptr_transf_partial ; eauto.
Qed.

Lemma sig_fundef_translated:
  forall f tf,
    wf_cssa_fundef f ->
    transl_fundef f = Errors.OK tf ->
    RTLpar.funsig tf = CSSA.funsig f.
Proof.
  intros f tf. intros.
  case_eq f; intros.
  - rewrite H1 in H0.
    simpl in *. Errors.monadInv H0.
    eapply transl_function_charact in EQ ; eauto.
    simpl in *.
    inv EQ.
    inv H. auto.
    inv H. auto.
  - rewrite H1 in H0. go.
Qed.

Ltac split_but_remember := 
    match goal with
    | [ H: _ |- ?A /\ ?B ] => assert(Hstep: A)
    end.

Ltac do_reachability REACH x :=
    inv REACH;
    match goal with
    | [ Hreach: exists t : trace, exists s0: state, _ |- _ ] =>
        destruct Hreach as [t [s0 Hreach]];
        destruct Hreach as [Hinit Hreachstep];
        constructor 1 with (x := x); go;
        exists t; exists s0; des_safe;
        esplits; auto;
        eapply star_right; go;
        rewrite E0_right; auto
    end.

    (* match goal with *)
    (*   | Hreach:exists (t : trace) (s0 : state), _ *)
    (*                                        |- _ => *)
    (*       destruct Hreach as [t [s0 Hreach]]; destruct Hreach as [Hinit Hreachstep]; constructor 1 with (x := x); go; exists t; *)
    (*       exists s0; des_safe; esplits; auto; eapply star_right; go; rewrite E0_right; auto *)
    (*   end. *)
(* Ltac do_reachability REACH x := *)
(*     inv REACH; *)
(*     match goal with *)
(*     | [ Hreach: exists t : trace, _ |- _ ] => *)
(*         destruct Hreach as [t Hreach]; *)
(*         destruct Hreach as [Hinit Hreachstep]; *)
(*         constructor 1 with (x := x); go; *)
(*         exists t; *)
(*         split; auto; *)
(*         eapply star_right; go; *)
(*         rewrite E0_right; auto *)
(*     end. *)

Lemma predecessors_preserved :
  forall f tf,
  wf_cssa_function f ->
  transl_function f = Errors.OK tf ->
  make_predecessors (RTLpar.fn_code tf) successors_instr
    = make_predecessors (fn_code f) successors_instr.
Proof.
    intros.
    exploit transl_function_correct; eauto.
    apply transl_function_charact; eauto. intros SPEC.
    inv SPEC.
    eapply same_successors_same_predecessors; eauto.
    intros.
    repeat rewrite PTree.gmap1.
    unfold option_map; flatten.
    assert((RTLpar.fn_code tf) ! i
      = Some (transl_instruction regrepr i1)).
    auto.
    assert (RW: i0 = transl_instruction regrepr i1)
      by congruence.
    rewrite RW.
    destruct i1; simpl; flatten; auto.
    assert((RTLpar.fn_code tf) ! i = None).
    apply codeNone; auto.
    congruence.
    assert((RTLpar.fn_code tf) ! i =
      Some (transl_instruction regrepr i0)).
    auto.
    congruence.
Qed.

Lemma jp_preserved_1 :
  forall f tf jp,
  wf_cssa_function f ->
  transl_function f = Errors.OK tf ->
  join_point jp f ->
  RTLpar.join_point jp tf.
Proof.
  intros. 
  inv H1.
  apply RTLpar.jp_cons with (l := l).
  exploit transl_function_correct; eauto.
  apply transl_function_charact; eauto. intros SPEC.
  inv SPEC.
  exploit predecessors_preserved; eauto.
  go. auto.
Qed.

Lemma jp_preserved_2 :
  forall f tf jp,
  wf_cssa_function f ->
  transl_function f = Errors.OK tf ->
  RTLpar.join_point jp tf ->
  join_point jp f.
Proof.
  intros.
  inv H1.
  apply jp_cons with (l := l).
  exploit transl_function_correct; eauto.
  apply transl_function_charact; eauto. intros SPEC.
  inv SPEC.
  exploit predecessors_preserved; eauto.
  go. auto.
Qed.

Lemma lazydef_spec :
  forall f pc r,
  lazydef f r pc \/ ~ lazydef f r pc.
Proof.
  intros.
  apply classic.
Qed.

Lemma live_implies_use :
  forall f pc r,
  wf_cssa_function f ->
  cssalive_spec f r pc ->
  exists pc', use f r pc'.
Proof.
  intros f pc r WF Hlive.
  induction Hlive; go.
Qed.

Lemma cssadom_dom :
  forall f pc r d,
  wf_cssa_function f ->
  ~ join_point pc f ->
  def f r d ->
  cssadom f r pc ->
  dom f d pc.
Proof.
  intros f pc r d WF Hnjp Hdef Hdom.
  inv Hdom.
  + assert(EQ: d = def_r).
    eapply def_def_eq; eauto.
    rewrite EQ in *.
    exploit (@sdom_spec positive); eauto.
    intros Hsdom.
    destruct Hsdom. auto.
  + inv H.
    induction WF.
    assert(Hphinotnone: (fn_phicode f) ! pc <> None) by congruence.
    rewrite <- fn_phicode_inv in Hphinotnone.
    congruence.
  + congruence.
Qed.

Lemma not_parcb_def_outside_inop :
  forall f pc r,
  wf_cssa_function f ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  ~ assigned_parcopy_spec (fn_parcopycode f) pc r.
Proof.
  intros f pc r WF Hnotinop.
  unfold not; intros Hassign.
  inv Hassign.
  assert(Hinop: exists s, (fn_code f) ! pc = Some (Inop s)).
  eapply parcb_inop; eauto. go.
  destruct Hinop; congruence.
Qed.

Lemma not_phi_def_outside_inop :
  forall f pc r,
  wf_cssa_function f ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  ~ assigned_phi_spec (fn_phicode f) pc r.
Proof.
  intros f pc r WF Hnotinop.
  unfold not; intros Hassign.
  inv Hassign.
  assert(Hinop: exists s, (fn_code f) ! pc = Some (Inop s)).
  eapply fn_inop_in_jp; go.
  destruct Hinop; go.
Qed.

Lemma not_lazydef_outside_inop :
  forall f pc r,
  wf_cssa_function f ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  ~ lazydef f r pc.
Proof.
  intros f pc r WF Hnotinop.
  unfold not; intros Hlazy.
  inv Hlazy.
  + contradict H.
    apply not_phi_def_outside_inop; go.
  + contradict H.
    apply not_parcb_def_outside_inop; go.
Qed.

Lemma not_lazydef_outside_jp :
  forall f pc r,
  wf_cssa_function f ->
  ~ join_point pc f ->
  ~ lazydef f r pc.
Proof.
  intros f pc r WF Hnojp.
  unfold not; intros Hlazy.
  inv Hlazy; auto.
  inv H.
  induction WF.
  rewrite fn_phicode_inv in Hnojp.
  intuition congruence.
Qed.

Lemma use_usecode_outside_inop :
  forall f pc r,
  wf_cssa_function f ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  use f r pc ->
  use_code f r pc.
Proof.
  intros f pc r WF Hnotinop Huse.
  inv Huse.
  + auto.
  + inv H.
    assert((fn_code f) ! pc = Some (Inop pc0)).
    apply fn_normalized; go.
    apply fn_phicode_inv; go.
    unfold successors_list; unfold successors in *.
    rewrite PTree.gmap1.
    assert(Hedge: cfg f pc pc0).
    {
      exploit pred_is_edge_help; go.
      intros. inv H. go.
    }
    case_eq ((fn_code f) ! pc); intros; try destruct i; simpl;
      flatten;
    inv Hedge;
    match goal with
    | [ H : (fn_code f) ! pc = Some ?i |- _ ] =>
      assert(Hins: ins = i) by congruence;
      rewrite Hins in HCFG_in;
      simpl in HCFG_in; auto
    | _ => idtac
    end.
    go. go.
  + inv H.
    assert(Hinop: exists s, (fn_code f) ! pc = Some (Inop s)).
    eapply parcb_inop; eauto. go.
    destruct Hinop. congruence.
Qed.

Hint Resolve ident_eq: core.

Lemma cssaval_contradiction_in_Ioporbuiltin :
  forall f pc args res pc' r s sp rs m,
  reachable prog (State s f sp pc rs m) ->
  wf_cssa_function f ->
  (exists op, (fn_code f) ! pc = Some (Iop op args res pc')) \/
  (exists fd r0,
    (fn_code f) ! pc = Some (Icall (funsig fd) (inl r0) args res pc')) \/
  (exists fd i,
    (fn_code f) ! pc = Some (Icall (funsig fd) (inr i) args res pc')) \/
  (exists chunk addr,
    (fn_code f) ! pc = Some (Iload chunk addr args res pc')) \/
  (exists ef args, (fn_code f) ! pc = Some (Ibuiltin ef args (BR res) pc')) ->
  cssaval_spec f (compute_cssaval_function f) ->
  compute_cssaval_function f r = compute_cssaval_function f res ->
  compute_cssaval_function f res = res ->
  r <> res ->
  cssalive_spec f r pc ->
  False.
Proof.
  intros until m.
  intros Hreach WF Hop Hcssavalspec Hcssavaleq Hcssavalins Hneq Hlive.
  rewrite Hcssavalins in Hcssavaleq.
  assert(cssadom f r pc).
  { assert(Hdomentry: cssadom f r pc \/
      (pc = fn_entrypoint f)).
    apply CSSAlive.live_cssadom; auto.
    decompose [or] Hop;
    try decompose record H; try decompose record H0;
    eapply fn_code_reached; eauto.
    inv Hdomentry. auto.
    assert((fn_parcopycode f) ! (fn_entrypoint f) = None)
     by (eapply fn_no_parcb_at_entry; eauto).
    decompose [or] Hop;
    try decompose record H1;
    try decompose record H0;
    exploit fn_entry; eauto; intros Hcodeinop;
    destruct Hcodeinop; congruence. }
  assert(Hdef: def f r (compute_def f (get_all_def f) r)).
  {
    exploit live_implies_use; eauto; intros Huse.
    destruct Huse as [pc'0 Huse].
    exploit exists_def; eauto; intros Hdef.
    destruct Hdef as [d Hdef].
    assert(compute_def f (get_all_def f) r = d).
    apply compute_def_correct; auto.
    congruence.
  }
  assert(Hdompcr: dom f pc (compute_def f (get_all_def f) r)).
  apply cssaval_dom with (r := r)
    (R := compute_cssaval_function f);
    decompose [or] Hop; try decompose record H1;
    try decompose record H0; go.
  assert(Hdomrpc: dom f (compute_def f (get_all_def f) r) pc).
  apply cssadom_dom with (r := r); eauto.
  unfold not; intros Hjp.
  rewrite fn_phicode_inv in Hjp; auto.
  assert(Hinop: exists s, (fn_code f) ! pc = Some (Inop s)).
  induction WF.
  apply fn_inop_in_jp. auto. destruct Hinop.
  decompose [or] Hop; try decompose record H1;
    try decompose record H2; congruence.
  assert(HEQ: pc = compute_def f (get_all_def f) r).
  eapply dom_antisym; eauto; destruct Hop; eauto.
  rewrite <- HEQ in *.
  inv Hdef; go.
  + rewrite <- H2 in Hop.
    assert(Hinop: exists s,
      (fn_code f) ! (fn_entrypoint f) = Some (Inop s)).
    induction WF.
    apply fn_entry. destruct Hinop;
      decompose [or] Hop;
      try decompose record H4;
      try decompose record H3; try congruence.
  + inv H0;
      decompose [or] Hop;
      try decompose record H0;
      try decompose record H2; go.
  + contradict H0;
      decompose [or] Hop;
      try decompose record H0;
      try decompose record H1; try congruence;
    apply not_phi_def_outside_inop; go.
  + contradict H0;
      decompose [or] Hop;
      try decompose record H0;
      try decompose record H1; try congruence;
    apply not_parcb_def_outside_inop; go.
Qed.

Lemma cssaval_contradiction_in_Iop :
  forall f pc op args res pc' r s sp rs m,
  reachable prog (State s f sp pc rs m) ->
  wf_cssa_function f ->
  (fn_code f) ! pc = Some (Iop op args res pc') ->
  cssaval_spec f (compute_cssaval_function f) ->
  compute_cssaval_function f r = compute_cssaval_function f res ->
  compute_cssaval_function f res = res ->
  r <> res ->
  cssalive_spec f r pc ->
  False.
Proof.
  intros.
  eapply cssaval_contradiction_in_Ioporbuiltin; eauto 6.
Qed.

Lemma cssaval_contradiction_in_Ibuiltin :
  forall f pc ef args res pc' r s sp rs m,
  reachable prog (State s f sp pc rs m) ->
  wf_cssa_function f ->
  (fn_code f) ! pc = Some (Ibuiltin ef args (BR res) pc') ->
  cssaval_spec f (compute_cssaval_function f) ->
  compute_cssaval_function f r = compute_cssaval_function f res ->
  compute_cssaval_function f res = res ->
  r <> res ->
  cssalive_spec f r pc ->
  False.
Proof.
  intros.
  eapply cssaval_contradiction_in_Ioporbuiltin; eauto 7.
  Unshelve. go.
Qed.

Lemma cssaval_contradiction_in_Icall :
  forall f pc fd args res pc' r r0 s sp rs m,
  reachable prog (State s f sp pc rs m) ->
  wf_cssa_function f ->
  (fn_code f) ! pc = Some (Icall (funsig fd) (inl r0) args res pc') ->
  cssaval_spec f (compute_cssaval_function f) ->
  compute_cssaval_function f r = compute_cssaval_function f res ->
  compute_cssaval_function f res = res ->
  r <> res ->
  cssalive_spec f r pc ->
  False.
Proof.
  intros.
  eapply cssaval_contradiction_in_Ioporbuiltin; eauto 6.
Qed.

Lemma cssaval_contradiction_in_Icallinr :
  forall f pc fd args res pc' r i s sp rs m,
  reachable prog (State s f sp pc rs m) ->
  wf_cssa_function f ->
  (fn_code f) ! pc = Some (Icall (funsig fd) (inr i) args res pc') ->
  cssaval_spec f (compute_cssaval_function f) ->
  compute_cssaval_function f r = compute_cssaval_function f res ->
  compute_cssaval_function f res = res ->
  r <> res ->
  cssalive_spec f r pc ->
  False.
Proof.
  intros.
  eapply cssaval_contradiction_in_Ioporbuiltin; eauto 6.
Qed.

Lemma cssaval_contradiction_in_Iload :
  forall f pc args chunk addr dst pc' r s sp rs m,
  reachable prog (State s f sp pc rs m) ->
  wf_cssa_function f ->
  (fn_code f) ! pc = Some (Iload chunk addr args dst pc') ->
  cssaval_spec f (compute_cssaval_function f) ->
  compute_cssaval_function f r = compute_cssaval_function f dst ->
  compute_cssaval_function f dst = dst ->
  r <> dst ->
  cssalive_spec f r pc ->
  False.
Proof.
  intros.
  eapply cssaval_contradiction_in_Ioporbuiltin; eauto 7.
Qed.

Lemma not_lazydef_after_noinop :
  forall f pc pc' r,
  wf_cssa_function f ->
  cfg f pc pc' ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  ~ lazydef f r pc'.
Proof.
  intros f pc pc' r WF Hedge Hnotinop.
  unfold not; intros Hlazy.
  inv Hlazy.
  + inv H.
    assert(Hinop: (fn_code f) ! pc = Some (Inop pc')).
    induction WF.
    apply fn_normalized.
    apply fn_phicode_inv. congruence.
    unfold successors_list; unfold successors in *.
    rewrite PTree.gmap1.
    case_eq ((fn_code f) ! pc); intros; try destruct i; simpl;
      flatten;
    inv Hedge;
    match goal with
    | [ H : (fn_code f) ! pc = Some ?i |- _ ] =>
      assert(Hins: ins = i) by congruence;
      rewrite Hins in HCFG_in;
      simpl in HCFG_in; auto
    | _ => idtac
    end.
    go.  go.
  + assert(Hinop: (fn_code f) ! pc = Some (Inop pc')).
    apply fn_normalized; go.
    unfold successors_list; unfold successors in *.
    rewrite PTree.gmap1.
    case_eq ((fn_code f) ! pc); intros; try destruct i; simpl;
      flatten;
    inv Hedge;
    match goal with
    | [ H : (fn_code f) ! pc = Some ?i |- _ ] =>
      assert(Hins: ins = i) by congruence;
      rewrite Hins in HCFG_in;
      simpl in HCFG_in; auto
    | _ => idtac
    end.
    go. go.
Qed.

Lemma live_in_pred_if_notdefined :
  forall f r pc pc',
  wf_cssa_function f ->
  ~ def f r pc ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  cfg f pc pc' ->
  cssalive_spec f r pc' /\ ~ lazydef f r pc' \/ lazydef f r pc' ->
  cssalive_spec f r pc.
Proof.
  intros f r pc pc' WF Hnotdef Hnotinop Hedge Hprops.
  destruct Hprops as [Hlive | Hlazy].
  + constructor 2 with (pc' := pc').
    go.
    unfold not; intros Hdef.
    inv Hdef; go.
    tauto.
  + contradict Hlazy.
    eapply not_lazydef_after_noinop; go.
Qed.

Lemma live_at_notinop_if_used :
  forall f pc r,
  wf_cssa_function f ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  use f r pc ->
  cssalive_spec f r pc.
Proof.
  intros f pc r WF Hnotinop Huse.
  constructor.
  unfold not; intros Hdef.
  inv Hdef.
  + induction WF.
    destruct fn_entry; go.
  + assert(Husecode: use_code f r pc).
    apply use_usecode_outside_inop; auto.
    eapply fn_use_def_code; eauto.
  + contradict H.
    apply not_phi_def_outside_inop; go.
  + contradict H.
    apply not_parcb_def_outside_inop; go.
  + auto.
Qed.

Lemma not_usedanddef_outside_inop :
  forall f pc r,
  wf_cssa_function f ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  use f r pc ->
  ~ def f r pc.
Proof.
  intros f pc r WF Hnotinop Huse.
  unfold not; intros.
  inv H.
  + assert(Hinop: exists s,
      (fn_code f) ! (fn_entrypoint f) = Some (Inop s)).
    induction WF.
    apply fn_entry. destruct Hinop; congruence.
  + assert(Husecode: use_code f r pc).
    apply use_usecode_outside_inop; auto.
    eapply fn_use_def_code; eauto.
  + contradict H0.
    apply not_phi_def_outside_inop; go.
  + contradict H0.
    apply not_parcb_def_outside_inop; go.
Qed.

Lemma absurd_notinop_at_entry :
  forall f,
  wf_cssa_function f ->
  (forall s, (fn_code f) ! (fn_entrypoint f) <> Some (Inop s)) ->
  False.
Proof.
  intros.
  assert(Hinop:
    exists s, (fn_code f) ! (fn_entrypoint f) = Some (Inop s)).
  induction H; go.
  destruct Hinop; go.
Qed.

Lemma ninterlive_outside_inop :
  forall f r dst pc pc',
  wf_cssa_function f ->
  cssalive_spec f r pc' /\ ~ lazydef f r pc' \/ lazydef f r pc' ->
  ninterlive_spec f r dst ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  def f dst pc ->
  cfg f pc pc' ->
  r <> dst ->
  False.
Proof.
  intros until pc'.
  intros WF Hprops Hninterlive Hnotinop Hdefdst Hedge Hneq.
  inv Hninterlive.
  assert(EQ: d2 = pc).
  eapply def_def_eq; eauto.
  rewrite EQ in *.
  assert(cssalive_spec f r pc').
  {
    destruct Hprops as [Hlive | Hlazy].
    destruct Hlive. auto.
    contradict Hlazy.
    apply not_lazydef_after_noinop with (pc := pc); go.
  }
  assert(cssaliveout_spec f r pc).
  eapply correspondance_outin; eauto. go.
Qed.

Lemma live_props_outside_inop :
  forall f r pc' pc,
  wf_cssa_function f ->
  cfg f pc pc' ->
  ~ assigned_code_spec (fn_code f) pc r ->
  cssalive_spec f r pc' /\ ~ lazydef f r pc' \/ lazydef f r pc' ->
  (forall s, (fn_code f) ! pc <> Some (Inop s)) ->
  cssalive_spec f r pc.
Proof.
  intros until pc.
  intros WF Hedge Hnotassign Hprops Hnotinop.
  apply live_in_pred_if_notdefined with (pc' := pc'); go.
  destruct Hprops as [Hlive | Hlazy].
  - unfold not; intros Hdef.
    inv Hdef; go.
    apply absurd_notinop_at_entry with (f := f); go.
    contradict H.
    apply not_phi_def_outside_inop; go.
    contradict H.
    apply not_parcb_def_outside_inop; go.
  - contradict Hlazy.
    eapply not_lazydef_after_noinop; go.
Qed.

Lemma functions_translated:
  forall (v: val) (f: CSSA.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf
    /\ transl_fundef f = Errors.OK tf.
Proof.
  eapply Genv.find_funct_transf_partial; eauto.
Qed.

Lemma spec_ros_r_find_function:
  forall rs rs' f r regrepr m,
  rs # r = rs' # (regrepr r) ->
  CSSA.find_function ge (CSSA.ros_to_vos m (inl _ r) rs) rs = Some f ->
  exists tf,
    RTLpar.find_function tge (RTLpar.ros_to_vos m (inl _ (regrepr r)) rs') rs' = Some tf
  /\ transl_fundef f = Errors.OK tf.
Proof.
  intros.
  ss. des_ifs.
  - exploit (functions_translated (Vptr b (Ptrofs.repr z))); eauto.
  - exploit (functions_translated (Vptr b i)); eauto.
Qed.

Lemma spec_ros_id_find_function:
  forall rs rs' f id m,
  CSSA.find_function ge (CSSA.ros_to_vos m (inr _ id) rs) rs = Some f ->
  exists tf,
     RTLpar.find_function tge (RTLpar.ros_to_vos m (inr _ id) rs') rs' = Some tf
  /\ transl_fundef f = Errors.OK tf.
Proof.
  intros.
  simpl in *.
  case_eq (Genv.find_symbol ge id) ; intros.
  rewrite H0 in H.
  rewrite symbols_preserved in * ; eauto ; rewrite H0 in *.
  exploit function_ptr_translated; eauto.
  rewrite H0 in H ; inv H.
Qed.

Lemma match_regset_args :
  forall args regrepr rs (rs' : SSA.regset),
  (forall r, In r args ->
    rs # r = rs' # (regrepr r)) ->
  rs ## args = rs' ## (map regrepr args).
Proof.
  induction args; go.
  intros.
  simpl.
  erewrite IHargs; eauto.
  rewrite H. auto. auto.
Qed.

Lemma not_used_at_entry :
  forall f r,
  wf_cssa_function f ->
  ~ use f r (fn_entrypoint f).
Proof.
  intros; unfold not; intros.
  inv H0.
  + exploit fn_entry; eauto; intros.
    destruct H0.
    inv H1; go.
  + inv H1.
    assert(HInpreds: In (fn_entrypoint f) (get_preds f) !!! pc).
    apply make_predecessors_correct_1
      with (instr := Inop pc).
    exploit fn_entry; eauto. intros.
    exploit pred_is_edge_help; eauto; intros.
    exploit is_edge_insuccs; eauto; intros.
    destruct H0. destruct H2. destruct H2.
    unfold successors in H2.
    rewrite PTree.gmap1 in H2.
    unfold option_map in H2.
    rewrite H0 in H2. simpl in H2.
    assert(EQ: x0 = x :: nil) by congruence.
    rewrite EQ in *.
    inv H3; auto. contradiction.
    simpl; auto.
    eapply parcbSome; eauto.
    eapply fn_no_parcb_at_entry; eauto.
  + inv H1.
    assert((fn_parcopycode f) ! (fn_entrypoint f) = None).
    eapply fn_no_parcb_at_entry; eauto.
    congruence.
Qed.

Lemma no_jp_after_entry :
  forall f pc,
  wf_cssa_function f ->
  (fn_phicode f) ! pc <> None ->
  cfg f (fn_entrypoint f) pc ->
  False.
Proof.
  intros f pc WF Hphibnotnone Hcfg.
  assert(HInpreds: In (fn_entrypoint f) (get_preds f) !!! pc).
  invh cfg; go.
  { apply make_predecessors_correct_1
      with (instr := Inop pc).
    exploit fn_entry; eauto. intros.
    destruct H.
    rewrite H in HCFG_ins.
    assert(Hins: Inop x = ins) by congruence.
    rewrite <- Hins in HCFG_in.
    simpl in *. destruct HCFG_in; try congruence. contradiction.
    simpl; auto. }
  case_eq ((fn_phicode f) ! pc); intros; try congruence.
  exploit parcbSome; eauto.
  eapply fn_no_parcb_at_entry; eauto.
Qed.

Lemma live_at_entry_def_aux:
  forall f r pc',
  wf_cssa_function f ->
  cfg f (fn_entrypoint f) pc' ->
  cssalive_spec f r pc' ->
  def f r (fn_entrypoint f).
Proof.
  intros f r pc' WF Hcfg Hlive.
  exploit CSSAlive.live_cssadom; eauto.
  constructor. auto.
  intros.
  destruct H; auto.
  + inv H.
    - inv H1.
      inv DOM; try congruence.
      specialize (PATH (fn_entrypoint f :: nil)).
      exploit PATH.
      go. intros Hin. inv Hin; try congruence. contradiction.
    - exfalso. eapply no_jp_after_entry; eauto.
      inv H0; congruence.
    - exfalso. eapply no_jp_after_entry; eauto.
      rewrite fn_phicode_inv in H1; auto.
  + rewrite H in *.
    contradict Hcfg.
    apply fn_entry_pred; auto.
Qed.

Lemma live_at_entry_def :
  forall f r,
  wf_cssa_function f ->
  cssalive_spec f r (fn_entrypoint f) ->
  def f r (fn_entrypoint f).
Proof.
  intros.
  induction H0.
  + contradict H1.
    apply not_used_at_entry; auto.
  + eapply live_at_entry_def_aux; eauto.
  + eapply live_at_entry_def_aux; eauto.
Qed.

Lemma init_regs_match :
  forall params f r d args regrepr,
  wf_cssa_function f ->
  cssalive_spec f r (fn_entrypoint f) ->
  (forall r', In r' params -> In r' (fn_params f)) ->
  compute_regrepr f = OK regrepr ->
  def f r d ->
  (init_regs args params) !! r =
    (init_regs args (map regrepr params))
      !! (regrepr r).
Proof.
  induction params;
  intros until regrepr; intros WF Hlive Hparams Hregrepr Hdef; simpl.
  rewrite PMap.gi.
  rewrite PMap.gi.
  auto.
  flatten; go.
  rewrite PMap.gi.
  rewrite PMap.gi.
  auto.
  case_eq (peq a r); intros.
  + rewrite e in *. repeat rewrite PMap.gss. auto.
  + rewrite PMap.gsspec.
    rewrite PMap.gsspec.
    flatten; auto.
    exploit compute_regrepr_correct; eauto; intros Hninterf.
    inv Hninterf.
    {
      inv H0.
      assert(compute_cssaval_function f a = a).
      apply H5. constructor. go.
      exploit live_at_entry_def; eauto; intros Hdefr.
      assert(compute_cssaval_function f r = r).
      {
        inv Hdefr.
        + apply H5. auto.
        + exploit fn_entry; eauto; intros Hinop.
          destruct Hinop.
          inv H6; go.
        + exploit fn_no_parcb_at_entry; eauto; intros.
          inv H6.
          exploit parcb'Some; eauto; intros. contradiction.
        + exploit fn_no_parcb_at_entry; eauto; intros.
          inv H6. congruence.
       }
       go.
    }
    { inv H0.
      assert(Hrdef: def f r (fn_entrypoint f)).
      apply live_at_entry_def; auto.
      assert(Heq: d1 = (fn_entrypoint f)).
      eapply def_def_eq; eauto.
      assert(Hdefa: def f a (fn_entrypoint f)).
      eauto.
      assert(Heq2: d2 = (fn_entrypoint f)).
      eapply def_def_eq; eauto.
      congruence.
    }
    eauto.
Qed.

Lemma liveorlazydef_exists_def:
  forall f r pc,
  wf_cssa_function f ->
  cssalive_spec f r pc /\ ~ lazydef f r pc \/ lazydef f r pc ->
  exists d, def f r d.
Proof.
  intros f r pc WH Hrprops.
  destruct Hrprops as [Hrprops | Hrprops]; auto.
  destruct Hrprops.
  exploit live_implies_use; eauto; intros Huse.
  destruct Huse as [u Huse].
  exploit exists_def; eauto.
  inv Hrprops; go.
Qed.

Lemma live_exists_def:
  forall f r pc,
  wf_cssa_function f ->
  cssalive_spec f r pc ->
  exists d, def f r d.
Proof.
  intros f r pc WF Hlive.
  exploit live_implies_use; eauto; intros Huse.
  destruct Huse as [u Huse].
  exploit exists_def; eauto.
Qed.

Lemma compute_regrepr_good_cssaval :
  forall f regrepr,
  compute_regrepr f = Errors.OK regrepr ->
  check_cssaval f (compute_cssaval_function f) 
    (get_ext_params f (get_all_def f)) = true.
Proof.
  intros.
  unfold compute_regrepr in *.
  flatten H; auto.
  unfold compute_ninterfere in Eq.
  flatten Eq.
  rewrite negb_false_iff in Eq3; eauto.
Qed.

Lemma senv_preserved:
  Senv.equiv (Genv.to_senv ge) (Genv.to_senv tge).
Proof.
  eapply Genv.senv_transf_partial; eauto.
Qed.

Lemma same_public:
  prog_public prog = prog_public tprog.
Proof. inv TRANSF_PROG. des; eauto. Qed.

Lemma transl_step_correct:
  forall s1 t s2,
  IStep sem s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2',
  DStep tsem s1' t s2' /\ match_states s2 s2'.
Proof.
  destruct 1. generalize dependent s2. rename H into INT.
  induction 1; intros; inv MS; auto;
  match goal with
    | [H : transl_fundef (Internal ?f) = _ |- _ ] => idtac
    | [H : transl_fundef (External ?f) = _ |- _ ] => idtac
    | [  |- context [RTLpar.Returnstate ?ts ?vres ?m]] => idtac
    | _ =>
      (exploit transl_function_charact; eauto; intros;
       exploit transl_function_correct; eauto; intros)
  end;
  match goal with
    | [SPEC: transl_function_spec ?f ?tf |- _ ] =>
      inv SPEC
    | _ => try (generalize (wf_cssa f) ; intros HWF)
  end.
  (* inop without block *)
  { exists (RTLpar.State ts tf sp pc' rs' m). split; auto.
    DStep_tac.
    { eapply codeSome in H; eauto. ss. clarify. }
    econstructor 1 ; eauto.
    - replace (Inop pc') with
        (transl_instruction regrepr (Inop pc')); auto.
    - intro Hcont. eelim H0; eauto using jp_preserved_2. 
    - econstructor; eauto.
      (* inv REACH. *)
  
      (* ; auto; eapply star_right; go; rewrite E0_right; auto *)
      (* match goal with *)
      (* | Hreach:exists t : trace, _ |- _ => *)
      (*     destruct Hreach as [t [s0 Hreach]]; destruct Hreach as [Hinit Hreachstep]; constructor 1 with (x := x); go; exists t; exist  *)
      (*     split; auto; eapply star_right; go; rewrite E0_right; auto *)
      (* end. *)
      do_reachability REACH x.
      econstructor; eauto; intros.
      inv MREG.
      eqregreprs regrepr0 regrepr.
      destruct H2.
      destruct H2 as [Hlive Hlazy].
      apply H3.
      generalize lazydef_spec; intros Hlazyspecg.
      assert(Hlazyspec: lazydef f r pc \/ ~ lazydef f r pc)
        by eauto.
      destruct Hlazyspec. auto. left.
      split; auto.
      case_eq (peq (fn_entrypoint f) pc).
      {
        intros. rewrite e in *.
        constructor 3 with (pc' := pc'); go.
      }
      (* constructor 1. *)
      constructor 2 with (pc' := pc').
      go.
      {
        unfold not; intros Hdef.
        inv Hdef; go.
        inv H5; go.
        assert(lazydef f r pc).
        go. congruence.
        assert(lazydef f r pc).
        constructor 2.
        auto.
        inv H5.
        induction WFF; eauto. (* use of parcbjp *)
        go.
      }
      go.
      inv H2; go.
      induction WFF. rewrite fn_phicode_inv in H0.
      inv H4; go. rewrite H2 in H0.
      assert (Some phiinstr <> None) by congruence.
      assert (~ (Some phiinstr <> None)) by auto.
      contradiction.
  }
  { (* inop with block *)
    exists (RTLpar.State ts tf sp pc'
      (parcopy_store (parcb_cleanup (transl_parcb regrepr parcb'))
        (parcopy_store (parcb_cleanup (transl_parcb regrepr parcb)) rs')) m).
    split_but_remember.
    {
      DStep_tac.
      { eapply codeSome in H; eauto. ss. clarify. }
      apply RTLpar.exec_Inop_jp ; auto.
      replace (Inop pc') with
        (transl_instruction regrepr (Inop pc')); auto.
      {
        eapply jp_preserved_1; eauto. 
      }
    }      
    split; auto.
    assert(Hreach: reachable prog
      (State s f sp pc'
        (parcopy_store parcb'
          (phi_store k phib (parcopy_store parcb rs))) m)).
    do_reachability REACH x.
    econstructor; eauto.
    econstructor; eauto.
    intros r Hrprops.
    exploit liveorlazydef_exists_def; eauto; intros DEF.
    destruct DEF as [d DEF].
    apply simul_parcbphibparcb'
      with (f := f) (pc := pc) (pc' := pc')
      (s := s) (sp := sp) (m := m) (d := d); eauto.
    exploit compute_regrepr_good_cssaval; eauto.
    destruct Hrprops as [Hrprops | Hrprops]; go.
    tauto.
  }
  { (* Iop *)
    exists (RTLpar.State ts tf sp pc' (rs'# (regrepr res) <- v) m).
    split_but_remember.
    {
      DStep_tac.
      { eapply codeSome in H; eauto. ss. clarify. }
      apply RTLpar.exec_Iop with (op := op) (args := map regrepr args).
      exploit codeSome; go.
      inv MREG.
      rewrite <- registers_equal with (rs := rs).
      erewrite eval_operation_wrapper_preserved; eauto.
      eapply symbols_preserved.
      intros.
      eqregreprs regrepr0 regrepr.
      apply H2.
      (* properties of [r] *)
      left. split; auto.
      eapply live_at_notinop_if_used; eauto.
      go. go.
      apply not_lazydef_outside_inop; go.
    }
    constructor; eauto.
    econstructor; eauto. intros.
    do_reachability REACH x.
    econstructor; eauto. intros.
    rewrite PMap.gsspec.
    rewrite PMap.gsspec.
    inv MREG.
    flatten.
    eqregreprs regrepr0 regrepr.
    exploit liveorlazydef_exists_def; eauto; intros DEF.
    exploit compute_regrepr_correct; eauto; intros Hninterf.
    inv Hninterf.
    assert(Hcssavalspec: cssaval_spec f (compute_cssaval_function f))
      by auto. (* copy of hypothesis *)
    inv Hcssavalspec.
    exploit H8; eauto; intros Hcssavalins.
    simpl in Hcssavalins.
    (* Cas [r <> res] et même ssa-valeur. Si [ins] n'est pas une
       copie, alors la ssa-valeur de [res] est [res], mais [r] a la
       même, c'est absurde, car il est censé dominer. Sinon, c'est une
       copie, dont la source est de même ssa-valeur que [r], donc même
       valeur ici, car celui-ci est vivant. *)
    {
      assert(cssalive_spec f r pc).
      eapply live_props_outside_inop; go.
      unfold not; intros Hassign; inv Hassign; go.
      flatten Hcssavalins;
      match goal with
      | [ H : compute_cssaval_function f res = res |- _ ] =>
          assert(False) by
           (eapply cssaval_contradiction_in_Iop; eauto);
          contradiction
      | _ => idtac
      end.
      assert(compute_cssaval_function f r0
        = compute_cssaval_function f r) by congruence.
      assert(rs !! r0 = rs !! r).
      apply cssaval_spec_correct_2
        with (prog := prog) (f := f)
          (pc := pc) (s := s) (sp := sp) (m := m);
        auto.
      {
        assert(Hdef: def f r0 (compute_def f (get_all_def f) r0)).
        {
          assert(Huse: use f r0 pc) by go.
          exploit exists_def; eauto; intros Hdef.
          destruct Hdef as [d Hdef].
          assert(compute_def f (get_all_def f) r0 = d).
          apply compute_def_correct; auto.
          congruence.
        }
        assert (dom f (compute_def f (get_all_def f) r0) pc).
        apply fn_strict with (x := r0); go.
        constructor 1 with (def_r := compute_def f (get_all_def f) r0);
          auto.
        constructor. auto.
        unfold not; intros Heq.
        rewrite Heq in Hdef.
        assert(use f r0 pc) by go.
        contradict Hdef.
        apply not_usedanddef_outside_inop; go.
      }
      { assert(Hdomentry: cssadom f r pc \/
          (pc = fn_entrypoint f)).
        apply CSSAlive.live_cssadom; auto.
        eapply fn_code_reached; eauto.
        inv Hdomentry.
        assert((fn_parcopycode f) ! (fn_entrypoint f) = None)
         by (eapply fn_no_parcb_at_entry; eauto).
        congruence.
        exploit fn_entry; eauto. intros Hinop. destruct Hinop.
        congruence. }
      unfold cssaval. flatten.
      exploit compute_regrepr_good_cssaval; eauto.
      intros. congruence.
      rewrite eval_operation_no_ptr_op in H0; ss.
      go.
    }
    { exfalso. eapply ninterlive_outside_inop; go. go. }
    eqregreprs regrepr0 regrepr.
    apply H3. left.
    split.
    + eapply live_props_outside_inop; go.
      unfold not; intros Hassign; inv Hassign; go.
    + apply not_lazydef_outside_inop; go.
  }
  { (* Iload *)
    exists (RTLpar.State ts tf sp pc' (rs' # (regrepr dst) <- v) m).
    split_but_remember.
    {
      DStep_tac.
      { eapply codeSome in H; eauto. ss. clarify. }
      apply RTLpar.exec_Iload
        with (chunk := chunk) (addr := addr) (args := map regrepr args)
        (a := a).
      rewrite codeSome with (ins := (Iload chunk addr args dst pc'));
        go.
      rewrite <- registers_equal with (rs := rs).
      erewrite eval_addressing_preserved; eauto.
      eapply symbols_preserved.
      intros. inv MREG.
      eqregreprs regrepr0 regrepr.
      apply H4.
      left. split; auto.
      (* properties of [r] *)
      eapply live_at_notinop_if_used; eauto.
      go. go.
      apply not_lazydef_outside_inop; go.
      (* memory *)
      go.
    }
    constructor; eauto.
    econstructor; eauto; intros.
    do_reachability REACH x.
    econstructor; eauto; intros.
    rewrite PMap.gsspec.
    rewrite PMap.gsspec.
    inv MREG.
    flatten.
    eqregreprs regrepr0 regrepr.
    exploit liveorlazydef_exists_def; eauto; intros DEF.
    exploit compute_regrepr_correct; eauto; intros Hninterf.
    inv Hninterf.
    assert(Hcssavalspec: cssaval_spec f (compute_cssaval_function f))
      by auto. (* copy of hypothesis *)
    inv Hcssavalspec.
    exploit H9; eauto; intros Hcssavalins.
    simpl in Hcssavalins.
    (* Cas [r <> res] et même ssa-valeur. Si [ins] n'est pas une
       copie, alors la ssa-valeur de [res] est [res], mais [r] a la
       même, c'est absurde, car il est censé dominer. Sinon, c'est une
       copie, dont la source est de même ssa-valeur que [r], donc même
       valeur ici, car celui-ci est vivant. *)
    {
      assert(cssalive_spec f r pc).
      apply live_in_pred_if_notdefined with (pc' := pc'); go.
      {
        destruct H3 as [Hlive | Hlazy].
        +
          unfold not; intros Hdef.
          inv Hdef; go.
          apply absurd_notinop_at_entry with (f := f); go.
          induction WFF.
          inv H3; go.
          contradict H3.
          apply not_phi_def_outside_inop; go.
          contradict H3.
          apply not_parcb_def_outside_inop; go.
        + contradict Hlazy.
          apply not_lazydef_after_noinop with (pc := pc); go.
      }
      assert(False) by
       (eapply cssaval_contradiction_in_Iload; eauto);
      contradiction.
    }
    exfalso. eapply ninterlive_outside_inop; go. go.
    eqregreprs regrepr0 regrepr.
    apply H4. left.
    split.
    + eapply live_props_outside_inop; go.
      unfold not; intros Hassign; inv Hassign; go.
    + apply not_lazydef_outside_inop; go.
  }
  { (* Istore *)
    exists (RTLpar.State ts tf sp pc' rs' m').
    split_but_remember.
    { DStep_tac.
      { eapply codeSome in H; eauto. ss. clarify. }
      apply RTLpar.exec_Istore with (chunk := chunk)
        (addr := addr) (args := map regrepr args) (src := regrepr src)
        (a := a).
      rewrite codeSome with
        (ins := (Istore chunk addr args src pc'));
        go.
      rewrite <- registers_equal with (rs := rs).
      erewrite eval_addressing_preserved; eauto.
      eapply symbols_preserved.
      intros. inv MREG.
      eqregreprs regrepr0 regrepr.
      apply H4. left.
      (* properties of [r] *)
      split; auto.
      eapply live_at_notinop_if_used; eauto.
      go. go.
      apply not_lazydef_outside_inop; go.
      inv MREG.
      eqregreprs regrepr0 regrepr.
      rewrite <- H3.
      go.
      left. split.
      + constructor.
        unfold not; intros Hdef.
        inv Hdef; go.
        apply absurd_notinop_at_entry with (f := f); go.
        induction WFF.
        inv H4; go.
        contradict H4.
        apply not_phi_def_outside_inop; go.
        contradict H4.
        apply not_parcb_def_outside_inop; go.
        go.
      + apply not_lazydef_outside_inop; go.
    }
    constructor; eauto.
    constructor; eauto.
    do_reachability REACH x.
    econstructor; eauto.
    intros.
    inv MREG.
    eqregreprs regrepr0 regrepr.
    apply H4. left.
    split.
    + eapply live_props_outside_inop; go.
      unfold not; intros Hassign; inv Hassign; go.
    + apply not_lazydef_outside_inop; go.
  }
  { (* Icall *)
    assert (WFfd: wf_cssa_fundef fd).
    {
      unfold wf_ssa_program in WF_PROG.
      assert (ID: exists id,
        In (id, Gfun fd) (prog_defs prog)).
      unfold find_function in H0.
      unfold Genv.find_funct in H0.
      flatten H0;
        apply Genv.find_funct_ptr_inversion
          with (b := b); auto.
      destruct ID as [id Infd].
      apply WF_PROG with id.
      auto.
    }
    assert(RW: rs ## args = rs' ## (map regrepr args)).
    {
      apply match_regset_args.
      intros r Hin.
      inv MREG.
      eqregreprs regrepr0 regrepr.
      apply H2.
      left. split.
      eapply live_at_notinop_if_used; eauto.
      go. apply u_code.
      destruct ros.
      apply UIcall with (sig := (funsig fd))
        (r := r0) (args := args) (dst := res) (s := pc').
      go. go. go.
      apply not_lazydef_outside_inop; go.
    }
    destruct ros.
    + assert(Htfd: exists tfd,
        RTLpar.find_function tge (RTLpar.ros_to_vos m (inl _ (regrepr r)) rs') rs' = Some tfd
        /\ transl_fundef fd = Errors.OK tfd).
      {
        apply spec_ros_r_find_function
          with (rs := rs); auto.
        inv MREG.
        eqregreprs regrepr0 regrepr.
        apply H2. left.
        split.
        - eapply live_at_notinop_if_used; eauto.
          go. go.
        - apply not_lazydef_outside_inop; go.
      }
      destruct Htfd as [tfd Hfind].
      exists (RTLpar.Callstate
        (RTLpar.Stackframe (regrepr res) tf sp pc' rs' :: ts)
        tfd (rs' ## (map regrepr args)) m).
      split_but_remember.
      - DStep_tac; try by
        (eapply codeSome in H; eauto; ss; clarify).
        apply RTLpar.exec_Icall with (sig := RTLpar.funsig tfd)
          (ros := inl (regrepr r)).
        rewrite codeSome with
          (ins := (Icall (funsig fd) (inl r) args res pc'));
          go.
        simpl.
        rewrite sig_fundef_translated with (f := fd); go.
        tauto. tauto. auto.
      - split; auto.  
        rewrite <- RW.
        apply match_states_call.
        do_reachability REACH x.
        destruct Hfind. auto.
        econstructor; go.
        intros r0 Hprops.
        {
          assert(cssalive_spec f r0 pc).
          apply live_in_pred_if_notdefined with (pc' := pc'); go.
          {
            destruct Hprops as [Hlive | Hlazy].
            +
              decompose [and] Hlive.
              unfold not; intros Hdef.
              inv Hdef; go.
              apply absurd_notinop_at_entry with (f := f); go.
              induction WFF.
              inv H3; go.
              contradict H3.
              apply not_phi_def_outside_inop; go.
              contradict H3.
              apply not_parcb_def_outside_inop; go.
            + contradict Hlazy.
              apply not_lazydef_after_noinop with (pc := pc); go.
          }
          tauto.
          inv MREG.
          eqregreprs regrepr0 regrepr.
          apply H3. tauto.
        }
        intros.
        {
          unfold not; intros Hlive.
          assert(Hlivepc: cssalive_spec f r0 pc). 
          {
            econstructor 2; go.
            unfold not; intros Hdef.
            inv Hdef; go.
            apply absurd_notinop_at_entry with (f := f); go.
            induction WFF.
            inv H4; go.
            contradict H4.
            apply not_phi_def_outside_inop; go.
            contradict H4.
            apply not_parcb_def_outside_inop; go.
          }
          exploit live_exists_def; eauto; intros Hdef.
          destruct Hdef as [d Hdef].
          exploit compute_regrepr_correct; eauto; intros Hninterf.
          inv Hninterf.
          assert(Hcssavalspec:
            cssaval_spec f (compute_cssaval_function f))
            by auto. (* copy of hypothesis *)
          inv Hcssavalspec.
          exploit H8; eauto; intros Hcssavalins.
          simpl in Hcssavalins.
          apply cssaval_contradiction_in_Icall
            with (f := f) (pc := pc) (fd := fd)
              (args := args)
               (res := res) (pc' := pc')
              (r0 := r) (r := r0)
              (s := s) (sp := sp) (rs := rs) (m := m); go.
          inv H4.
          assert(cssaliveout_spec f r0 pc).
          apply correspondance_outin with (pc' := pc'); eauto. go.
          assert(d2 = pc).
          eapply def_def_eq; eauto.
          congruence.
        }
        intros.
        apply not_lazydef_after_noinop with (pc := pc); go.
        go. 
    + assert(Htfd: exists tfd,
        RTLpar.find_function tge (RTLpar.ros_to_vos m (inr i) rs') rs' = Some tfd
        /\ transl_fundef fd = Errors.OK tfd).
      apply spec_ros_id_find_function
        with (rs := rs); auto.
      destruct Htfd as [tfd Htfd].
      exists(RTLpar.Callstate
        (RTLpar.Stackframe (regrepr res) tf sp pc' rs' :: ts)
        tfd (rs' ## (map regrepr args)) m).
      split_but_remember.
      - DStep_tac.
        { eapply codeSome in H; eauto. ss. clarify. }
        { eapply codeSome in H; eauto. ss. clarify. }
        apply RTLpar.exec_Icall
          with (sig := RTLpar.funsig tfd) (ros := inr i).
        rewrite codeSome with
          (ins := (Icall (funsig fd) (inr i) args res pc'));
          go.
        simpl.
        rewrite sig_fundef_translated with (f := fd); go.
        tauto. tauto. auto.
      - split; auto.
        rewrite <- RW.
        apply match_states_call.
        do_reachability REACH x.
        destruct Htfd. auto.
        econstructor; go.
        intros r0 Hprops.
        {
          assert(cssalive_spec f r0 pc).
          apply live_in_pred_if_notdefined with (pc' := pc'); go.
          {
            destruct Hprops as [Hlive | Hlazy].
            +
              decompose [and] Hlive.
              unfold not; intros Hdef.
              inv Hdef; go.
              apply absurd_notinop_at_entry with (f := f); go.
              induction WFF.
              inv H3; go.
              contradict H3.
              apply not_phi_def_outside_inop; go.
              contradict H3.
              apply not_parcb_def_outside_inop; go.
            + contradict Hlazy.
              apply not_lazydef_after_noinop with (pc := pc); go.
          }
          tauto.
          inv MREG.
          eqregreprs regrepr0 regrepr.
          apply H3. tauto.
        }
        intros.
        {
          unfold not; intros Hlive.
          assert(Hlivepc: cssalive_spec f r pc). 
          {
            econstructor 2; go.
            unfold not; intros Hdef.
            inv Hdef; go.
            apply absurd_notinop_at_entry with (f := f); go.
            induction WFF.
            inv H4; go.
            contradict H4.
            apply not_phi_def_outside_inop; go.
            contradict H4.
            apply not_parcb_def_outside_inop; go.
          }
          exploit live_exists_def; eauto; intros Hdef.
          destruct Hdef as [d Hdef].
          exploit compute_regrepr_correct; eauto; intros Hninterf.
          inv Hninterf.
          assert(Hcssavalspec:
            cssaval_spec f (compute_cssaval_function f))
            by auto. (* copy of hypothesis *)
          inv Hcssavalspec.
          exploit H8; eauto; intros Hcssavalins.
          simpl in Hcssavalins.
          apply cssaval_contradiction_in_Icallinr
            with (f := f) (pc := pc) (fd := fd)
              (args := args)
               (res := res) (pc' := pc')
              (i := i) (r := r)
              (s := s) (sp := sp) (rs := rs) (m := m); go.
          inv H4.
          assert(cssaliveout_spec f r pc).
          apply correspondance_outin with (pc' := pc'); eauto. go.
          assert(d2 = pc).
          eapply def_def_eq; eauto.
          congruence.
        }
        intros.
        apply not_lazydef_after_noinop with (pc := pc); go.
        go. 
   }
   { (* Itailcall *)
     assert (WFfd: wf_cssa_fundef fd).
     {
       unfold wf_ssa_program in WF_PROG.
       assert (ID: exists id,
         In (id, Gfun fd) (prog_defs prog)).
       unfold find_function in H0.
       unfold Genv.find_funct in H0.
       flatten H0;
         apply Genv.find_funct_ptr_inversion
           with (b := b); auto.
       destruct ID as [id Infd].
       apply WF_PROG with id.
       auto.
     }
     assert(RW: rs ## args = rs' ## (map regrepr args)).
     {
       apply match_regset_args.
       intros r Hin.
       inv MREG.
       eqregreprs regrepr0 regrepr.
       apply H3.
       left. split.
       eapply live_at_notinop_if_used; eauto.
       go. apply u_code.
       destruct ros.
       apply UItailcall with (sig := (funsig fd))
         (r := r0) (args := args).
       go. go. go.
       apply not_lazydef_outside_inop; go.
     }
     destruct ros.
     + assert(Htfd: exists tfd,
         RTLpar.find_function tge (RTLpar.ros_to_vos m (inl _ (regrepr r)) rs') rs' = Some tfd
         /\ transl_fundef fd = Errors.OK tfd).
       {
         apply spec_ros_r_find_function
           with (rs := rs); auto.
         inv MREG.
         eqregreprs regrepr0 regrepr.
         apply H3. left.
         split.
         - eapply live_at_notinop_if_used; eauto.
           go. go.
         - apply not_lazydef_outside_inop; go.
       }
       destruct Htfd as [tfd Hfind].
       exists (RTLpar.Callstate
         ts tfd (rs' ## (map regrepr args)) m').
       split_but_remember.
       - DStep_tac; try by
         (eapply codeSome in H; eauto; ss; clarify).
         apply RTLpar.exec_Itailcall with (sig := RTLpar.funsig tfd)
           (ros := inl (regrepr r)).
         rewrite codeSome with
           (ins := (Itailcall (funsig fd) (inl r) args));
           go.
         simpl.
         rewrite sig_fundef_translated with (f := fd); go.
         tauto. tauto. auto.
         rewrite <- stacksize_preserved with (f := f); auto.
       - split; auto.  
         rewrite <- RW.
         apply match_states_call.
         do_reachability REACH x.
         destruct Hfind. auto.
         go. go.
     + assert(Htfd: exists tfd,
         RTLpar.find_function tge (RTLpar.ros_to_vos m (inr i) rs') rs' = Some tfd
         /\ transl_fundef fd = Errors.OK tfd).
       apply spec_ros_id_find_function
         with (rs := rs); auto.
       destruct Htfd as [tfd Htfd].
       exists(RTLpar.Callstate
         ts tfd (rs' ## (map regrepr args)) m').
       split_but_remember.
       - DStep_tac.
         { eapply codeSome in H; eauto. ss. clarify. }
         { eapply codeSome in H; eauto. ss. clarify. }
         apply RTLpar.exec_Itailcall
           with (sig := RTLpar.funsig tfd) (ros := inr i).
         rewrite codeSome with
           (ins := (Itailcall (funsig fd) (inr i) args));
           go.
         simpl.
         rewrite sig_fundef_translated with (f := fd); go.
         tauto. tauto. auto.
         rewrite <- stacksize_preserved with (f := f); auto.
       - split; auto.
         rewrite <- RW.
         apply match_states_call.
         do_reachability REACH x.
         destruct Htfd. auto.
         go. go.
  }
  { (* Ibuiltin *)
    exists (RTLpar.State ts tf sp pc' (regmap_setres  (map_builtin_res regrepr res)
                                                      vres rs') m'). 
    split_but_remember.
    { DStep_tac.
      { unfold is_internal in INT. ss. des_ifs.
        eapply codeSome in Heq0; eauto. ss. clarify. }
      eapply RTLpar.exec_Ibuiltin with(args := map (map_builtin_arg regrepr) args)
                                      (vargs := vargs)
                                      (res:= map_builtin_res regrepr res).
      rewrite codeSome with (ins := (Ibuiltin ef args res pc')); go.
      - inv MREG.
        eqregreprs regrepr0 regrepr.
        assert (forall r, In r (params_of_builtin_args args) -> rs !! r = rs' !! (regrepr r)).
        { intros. apply H3.
          left. split; auto.
          (* properties of [r] *)
          eapply live_at_notinop_if_used; eauto.
          go. go.
          apply not_lazydef_outside_inop; go.          
        }
        eapply eval_builtin_args_preserved with (ge1:= ge).
        apply senv_preserved.
        revert H0 H4. clear.
        induction 1 ; intros; go.
        simpl. constructor.
        + clear H0 IHlist_forall2.
          revert H H4.
          induction 1 ; intros ; simpl ; go.
          * rewrite H4; go.
          * { constructor.
              - eapply IHeval_builtin_arg1; eauto.
                intros. eapply H4; eauto. simpl in *.
                eapply in_app_or in H1.
                eapply in_or_app. intuition.
              - eapply IHeval_builtin_arg2; eauto.
                intros. eapply H4; eauto. simpl in *.
                eapply in_app_or in H1.
                eapply in_or_app. intuition.
            }
          * { constructor.
              - eapply IHeval_builtin_arg1; eauto.
                intros. eapply H4; eauto. simpl in *.
                eapply in_app_or in H1.
                eapply in_or_app. intuition.
              - eapply IHeval_builtin_arg2; eauto.
                intros. eapply H4; eauto. simpl in *.
                eapply in_app_or in H1.
                eapply in_or_app. intuition.
            }
        + eapply IHlist_forall2; eauto.
          intros. eapply H4. go.
      - eapply external_call_symbols_preserved; eauto.
        eapply senv_preserved. 
    }
    constructor; eauto.
    constructor; eauto.
    {
      inv REACH.
      destruct H3 as [tt Hreach].
      destruct Hreach as [s0 [Hinit [Hcap Hreachstep]]].
      constructor 1 with (x := x); go.
      des_safe.
      exists (Eapp tt t).
      exists s0.
      esplits; eauto.
      eapply star_right; go.
    }
    {
      econstructor; eauto; intros.
      inv MREG. rewrite RegRepr0 in RegRepr. inv RegRepr.
      destruct res ; simpl; go.
      - rewrite PMap.gsspec.
        rewrite PMap.gsspec.
        flatten.
        exploit liveorlazydef_exists_def; eauto; intros DEF.
        exploit compute_regrepr_correct; eauto; intros Hninterf.
        inv Hninterf.
        assert(Hcssavalspec: cssaval_spec f (compute_cssaval_function f))
        by auto. (* copy of hypothesis *)
        inv Hcssavalspec.
        exploit H9; eauto; intros Hcssavalins.
        simpl in Hcssavalins.
        {
        assert(cssalive_spec f r pc).
        apply live_in_pred_if_notdefined with (pc' := pc'); go.
        {
          destruct H3 as [Hlive | Hlazy].
          + unfold not; intros Hdef.
            inv Hdef; go.
            apply absurd_notinop_at_entry with (f := f); go.
            induction WFF.
            inv H3; go.
            contradict H3.
            apply not_phi_def_outside_inop; go.
            contradict H3.
            apply not_parcb_def_outside_inop; go.
          + contradict Hlazy.
            apply not_lazydef_after_noinop with (pc := pc); go.
        }
        assert(False) by
            (eapply cssaval_contradiction_in_Ibuiltin; eauto);
          contradiction.
      }
      exfalso. eapply ninterlive_outside_inop; go. go.
      apply H4. left.
      split.
      + eapply live_props_outside_inop; go.
        unfold not; intros Hassign; inv Hassign; go.
      + apply not_lazydef_outside_inop; go.
      - eapply H4; eauto.
        left. split.
        + eapply live_props_outside_inop; go.
          unfold not; intros Hassign; inv Hassign; go.
        + apply not_lazydef_outside_inop; go.
      - eapply H4; eauto.
        left. split.
        + eapply live_props_outside_inop; go.
          unfold not; intros Hassign; inv Hassign; go.
        + apply not_lazydef_outside_inop; go.
    }
  }
  
    { (* ifso *)
      exists (RTLpar.State ts tf sp ifso rs' m).
      split_but_remember.
      { DStep_tac.
        { eapply codeSome in H; eauto. ss. clarify. }
        apply RTLpar.exec_Icond_true
          with (cond := cond) (args := map regrepr args)
               (ifnot := ifnot).
        rewrite codeSome with
            (ins := (Icond cond args ifso ifnot));
          go.
        rewrite <- registers_equal with (rs := rs).
        eauto.
        intros.
        intros. inv MREG.
        eqregreprs regrepr0 regrepr.
        apply H3.
        left. split; auto.
        (* properties of [r] *)
        eapply live_at_notinop_if_used; eauto.
        go. go.
        apply not_lazydef_outside_inop; go.
      }
      + constructor; eauto.
        constructor; eauto.
        do_reachability REACH x.
        econstructor; eauto.
        intros.
        inv MREG.
        eqregreprs regrepr0 regrepr.
        apply H3. left.
        split.
      - apply live_props_outside_inop with (pc' := ifso); go.
        unfold not; intros Hassign; inv Hassign; go.
      - apply not_lazydef_outside_inop; go.
    }
    { (* ifnot *)
      exists (RTLpar.State ts tf sp ifnot rs' m).
      split_but_remember.
      { DStep_tac.
        { eapply codeSome in H; eauto. ss. clarify. }
        apply RTLpar.exec_Icond_false
          with (cond := cond) (args := map regrepr args)
               (ifso := ifso).
        rewrite codeSome with
            (ins := (Icond cond args ifso ifnot));
          go.
        rewrite <- registers_equal with (rs := rs).
        eauto.
        intros.
        intros. inv MREG.
        eqregreprs regrepr0 regrepr.
        apply H3.
        left. split; auto.
        (* properties of [r] *)
        eapply live_at_notinop_if_used; eauto.
        go. go.
        apply not_lazydef_outside_inop; go.
      }
      + constructor; eauto.
        constructor; eauto.
        do_reachability REACH x.
        econstructor; eauto.
        intros.
        inv MREG.
        eqregreprs regrepr0 regrepr.
        apply H3. left.
        split.
      - apply live_props_outside_inop with (pc' := ifnot); go.
        unfold not; intros Hassign; inv Hassign; go.
      - apply not_lazydef_outside_inop; go.
    }
    { (* ijumptable *)
      exists (RTLpar.State ts tf sp pc' rs' m).
      split_but_remember.
      { DStep_tac.
        { eapply codeSome in H; eauto. ss. clarify. }
        apply RTLpar.exec_Ijumptable with (arg := regrepr arg)
                                          (tbl := tbl) (n := n).
        rewrite codeSome with
            (ins := Ijumptable arg tbl);
          go.
        rewrite <- H0.
        symmetry.
        intros. inv MREG.
        eqregreprs regrepr0 regrepr.
        apply H3.
        left. split; auto.
        (* properties of [r] *)
        eapply live_at_notinop_if_used; eauto.
        go. go.
        apply not_lazydef_outside_inop; go.
        auto.
      }
      + constructor; eauto.
        constructor; eauto. intros.
        do_reachability REACH x.
        econstructor; eauto. intros r Hprops.
        inv MREG.
        eqregreprs regrepr0 regrepr.
        apply H3. left.
        split.
      - apply live_props_outside_inop with (pc' := pc'); go.
        econstructor; eauto. simpl.
        eapply list_nth_z_in; eauto.
        unfold not; intros Hassign; inv Hassign; go.
      - apply not_lazydef_outside_inop; go.
    }
    { (* ireturn *)
      destruct or.
      {
        exists (RTLpar.Returnstate ts (regmap_optget (Some (regrepr r)) Vundef rs') m').
        split_but_remember.
        { DStep_tac.
          { eapply codeSome in H; eauto. ss. clarify. }
          apply RTLpar.exec_Ireturn.
          rewrite codeSome with
              (ins := Ireturn (Some r));
            go.
          erewrite <- stacksize_preserved; eauto. }
        split; auto.
        simpl.
        inv MREG.
        eqregreprs regrepr0 regrepr.
        rewrite <- H2.
        apply match_states_return; go.
        {
          inv REACH.
          destruct H3 as [t Hreach].
          destruct Hreach as [s0 [Hinit [Hcap Hreachstep]]].
          econstructor; eauto.
          exists t.
          exists s0.
          splits; eauto.
          replace (Returnstate s rs !! r m')
            with (Returnstate s (regmap_optget (Some r) Vundef rs)
                              m').
          apply star_right
            with (t1 := t) (t2 := E0) (s2 :=
                                         (State s f (Vptr stk Ptrofs.zero) pc rs m)); go.
          eapply exec_Ireturn; go.
          symmetry.
          apply E0_right; go.
          go.
        }
        left. split.
        eapply live_at_notinop_if_used; eauto.
        go. go.
        apply not_lazydef_outside_inop; go.
      }
      exists (RTLpar.Returnstate ts (regmap_optget None Vundef rs') m').
      split; eauto.
      DStep_tac.
      { eapply codeSome in H; eauto. ss. clarify. }
      apply RTLpar.exec_Ireturn.
      rewrite codeSome with
          (ins := Ireturn None);
        go.
      erewrite <- stacksize_preserved; eauto.
      apply match_states_return; go.
      {
        inv REACH.
        destruct H2 as [t Hreach].
        destruct Hreach as [s0 [Hinit [Hcap Hreachstep]]].
        econstructor; eauto.
        exists t.
        exists s0.
        splits; eauto.
        apply star_right
          with (t1 := t) (t2 := E0) (s2 :=
                                       (State s f (Vptr stk Ptrofs.zero) pc rs m)); go.
        replace (regmap_optget None Vundef rs')
          with (regmap_optget None Vundef rs).
        eapply exec_Ireturn; go.
        auto.
        symmetry.
        apply E0_right; go.
      }
    }
    { (* internal *)
      destruct tf as [tf | tf].
      exists (RTLpar.State ts tf (Vptr stk Ptrofs.zero)
                           tf.(RTLpar.fn_entrypoint)
                                (init_regs args (RTLpar.fn_params tf)) m').
      split_but_remember.
      { DStep_tac.
        eapply RTLpar.exec_function_internal.
        erewrite <- stacksize_preserved; eauto.
        simpl in SPEC.
        unfold Errors.bind in SPEC.
        flatten SPEC. }
      split; auto.
      + simpl in *.
        unfold Errors.bind in SPEC.
        flatten SPEC.
        replace (RTLpar.fn_entrypoint tf) with (fn_entrypoint f).
        apply match_states_intro.
        do_reachability REACH x.
        go. go. induction WFF. auto.
        {
          unfold transl_function in Eq.
          flatten Eq; go.
          simpl.
          econstructor; eauto.
          intros.
          exploit liveorlazydef_exists_def; eauto;
            induction WFF; auto; intros DEF.
          destruct DEF as [d DEF].
          apply init_regs_match with (f := f) (d := d); auto.
          destruct H0; try tauto.
          contradict H0.
          apply not_lazydef_outside_jp.
          auto.
          unfold not; intros.
          apply fn_phicode_inv in H0; auto.
          case_eq((fn_phicode f) ! (fn_entrypoint f)); intros.
          assert(Hparcb: (fn_parcopycode f) ! (fn_entrypoint f) <> None).
          apply parcb'Some with (phib := p); eauto.
          contradict Hparcb.
          apply fn_no_parcb_at_entry with (f := f); auto.
          congruence.
        }
        unfold transl_function in Eq.
        flatten Eq. simpl. auto.
      + simpl in SPEC.
        unfold Errors.bind in SPEC.
        flatten SPEC.
    }
    { (* external *)
      inv SPEC.
      exists (RTLpar.Returnstate ts res m').
      split.
      + DStep_tac.
        eapply RTLpar.exec_function_external.
        eapply external_call_symbols_preserved; eauto.
        eapply senv_preserved. 
      + econstructor; eauto.
        {
          inv REACH.
          destruct H0 as [tt Hreach].
          destruct Hreach as [s0 [Hinit [Hcap Hreachstep]]].
          econstructor; eauto.
          exists (Eapp tt t).
          exists s0.
          splits; eauto.
          eapply star_right; go.
        }
    }
    { (* return state *)
      inv STACK.  
      exists (RTLpar.State ts0 tf sp pc (rs' # (regrepr res) <- vres) m).
      split.
      + DStep_tac. eapply RTLpar.exec_return.
      + econstructor; eauto.
        do_reachability REACH x.
        econstructor; eauto; intros.
        rewrite PMap.gsspec.
        rewrite PMap.gsspec.
        flatten.
        assert(~ cssalive_spec f r pc) by eauto.
        destruct H. tauto. contradict H. eauto.
        apply MRs. tauto.
    }
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
              exists st2, RTLpar.initial_state tprog st2
                          /\ match_init st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated ; eauto. intros [tf [Hfind Htrans]].
  econstructor; split.
  - econstructor.
    assert (MEM: (Genv.init_mem tprog) = Some m0) by (eapply (Genv.init_mem_transf_partial TRANSF_PROG); eauto).
    + apply MEM ; auto.
    + replace (prog_main tprog) with (prog_main prog). rewrite symbols_preserved; eauto.
      symmetry; eapply match_program_main; eauto.
    + eauto.
    + rewrite <- H3. apply sig_fundef_translated; auto.
      eapply Genv.find_funct_ptr_prop; eauto.
  - eapply match_init_intro; eauto.
    + eapply Genv.find_funct_ptr_prop ; eauto.  
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2
  -> final_state st1 r
  -> RTLpar.final_state st2 r.
Proof.
  intros. inv H0. inv H.
  inv STACK.
  constructor.
Qed.

Lemma match_states_bsim
      s1
      (EXT: is_external ge s1)
      s2 t s2'
      (STEPTGT: Step tsem s2 t s2')
      (MATCH: match_states s1 s2)
      (SAFESRC: safe sem s1)
  :
    (exists s1', Step sem s1 t s1' /\ match_states s1' s2').
Proof.
  assert (SEQUIV: Senv.equiv tge ge) by (symmetry; apply senv_preserved).
  unfold safe in SAFESRC. specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
  { inv SAFESRC. inv MATCH. inv STACK. inv STEPTGT. }
  inv MATCH; ss; des_ifs;
  match goal with
  | [H : transl_fundef (Internal ?f) = _ |- _ ] => idtac
  | [H : transl_fundef (External ?f) = _ |- _ ] => idtac
  | [  |- context [RTLpar.Returnstate ?ts ?vres ?m]] => idtac
  | _ =>
      (exploit transl_function_charact; eauto; intros;
       exploit transl_function_correct; eauto; intros)
  end;
  match goal with
  | [SPEC: transl_function_spec ?f ?tf |- _ ] =>
      inv SPEC
  | _ => try (generalize (wf_cssa f) ; intros HWF)
  end.
  (* builtin *)
  - exploit codeSome; eauto. i.
    inv STEPTGT; ss; clarify. inv SAFESRC; clarify.
    exists (State s f sp n (regmap_setres b vres rs) m').
    split_but_remember.
    { eapply CSSA.exec_Ibuiltin with (vargs:=vargs).
      - eauto.
      - assert (eval_builtin_args (Genv.globalenv tprog) (fun r : positive => rs' # r)
                  sp m (map (map_builtin_arg regrepr) l) vargs0).
        { inv MREG.
          eqregreprs regrepr0 regrepr.
          assert (forall r, In r (params_of_builtin_args l) -> rs !! r = rs' !! (regrepr r)).
          { intros. apply H0.
            left. split; auto.
            (* properties of [r] *)
            eapply live_at_notinop_if_used; eauto.
            go. go.
            apply not_lazydef_outside_inop; go.          
          }
          eapply eval_builtin_args_preserved with (ge1:= ge).
          apply senv_preserved.
          revert H12 H1. clear.
          induction 1 ; intros; go.
          simpl. constructor.
          + clear H12 IHlist_forall2.
            revert H H1.
            induction 1 ; intros ; simpl ; go.
            * rewrite H1; go.
            * { constructor.
                - eapply IHeval_builtin_arg1; eauto.
                  intros. eapply H1; eauto. simpl in *.
                  eapply in_app_or in H2.
                  eapply in_or_app. intuition.
                - eapply IHeval_builtin_arg2; eauto.
                  intros. eapply H1; eauto. simpl in *.
                  eapply in_app_or in H2.
                  eapply in_or_app. intuition.
              }
            * { constructor.
                - eapply IHeval_builtin_arg1; eauto.
                  intros. eapply H1; eauto. simpl in *.
                  eapply in_app_or in H2.
                  eapply in_or_app. intuition.
                - eapply IHeval_builtin_arg2; eauto.
                  intros. eapply H1; eauto. simpl in *.
                  eapply in_app_or in H2.
                  eapply in_or_app. intuition.
              }
          + eapply IHlist_forall2; eauto.
            intros. eapply H1. go. }
        exploit eval_builtin_args_determ. eapply H10. eapply H0. i. subst. eauto.
      - eapply external_call_symbols_preserved; eauto. }
    constructor; eauto.
    constructor; eauto.
    {
      inv REACH.
      destruct H0 as [tt Hreach].
      destruct Hreach as [s0 [Hinit [Hcap Hreachstep]]].
      constructor 1 with (x := x); go.
      exists (Eapp tt t).
      exists s0.
      splits; auto.
      eapply star_right; go.
    }
    {
      econstructor; eauto; intros.
      inv MREG. rewrite RegRepr0 in RegRepr. inv RegRepr.
      destruct b ; simpl; go.
      - rewrite PMap.gsspec.
        rewrite PMap.gsspec.
        flatten.
        exploit liveorlazydef_exists_def; eauto; intros DEF.
        exploit compute_regrepr_correct; eauto; intros Hninterf.
        inv Hninterf.
        assert(Hcssavalspec: cssaval_spec f (compute_cssaval_function f))
        by auto. (* copy of hypothesis *)
        inv Hcssavalspec.
        exploit H6; eauto; intros Hcssavalins.
        simpl in Hcssavalins.
        {
        assert(cssalive_spec f r pc).
        apply live_in_pred_if_notdefined with (pc' := n); go.
        {
          destruct H0 as [Hlive | Hlazy].
          + unfold not; intros Hdef.
            inv Hdef; go.
            apply absurd_notinop_at_entry with (f := f); go.
            induction WFF.
            inv H0; go.
            contradict H0.
            apply not_phi_def_outside_inop; go.
            contradict H0.
            apply not_parcb_def_outside_inop; go.
          + contradict Hlazy.
            apply not_lazydef_after_noinop with (pc := pc); go.
        }
        assert(False) by
            (eapply cssaval_contradiction_in_Ibuiltin; eauto);
          contradiction.
      }
      exfalso. eapply ninterlive_outside_inop; go. go.
      apply H1. left.
      split.
      + eapply live_props_outside_inop; go.
        unfold not; intros Hassign; inv Hassign; go.
      + apply not_lazydef_outside_inop; go.
      - eapply H1; eauto.
        left. split.
        + eapply live_props_outside_inop; go.
          unfold not; intros Hassign; inv Hassign; go.
        + apply not_lazydef_outside_inop; go.
      - eapply H1; eauto.
        left. split.
        + eapply live_props_outside_inop; go.
          unfold not; intros Hassign; inv Hassign; go.
        + apply not_lazydef_outside_inop; go.
    }
  (* external *)
  - inv SPEC.
    inv STEPTGT; ss; clarify. inv SAFESRC; clarify.
    exists (CSSA.Returnstate s res m').
    split.
    + eapply CSSA.exec_function_external.
      eapply external_call_symbols_preserved; eauto.
    + econstructor; eauto.
      {
        inv REACH.
        destruct H as [tt Hreach].
        destruct Hreach as [s0 [Hinit [Hcap Hreachstep]]].
        econstructor; eauto.
        exists (Eapp tt t).
        exists s0.
        splits; eauto.
        eapply star_right; go.
        econs; eauto. eapply external_call_symbols_preserved; eauto.
      }
Qed.

Lemma match_states_xsim
    st_src0 st_tgt0 gmtgt
    (MATCH: match_states st_src0 st_tgt0) :
  xsim (CSSA.semantics prog) (RTLpar.semantics tprog) gmtgt lt 0%nat st_src0 st_tgt0.
Proof.
  generalize dependent st_src0. generalize dependent st_tgt0.
  pcofix CIH. i. pfold.
  destruct (classic (CSSA.is_external ge st_src0)); cycle 1.
  (* not external *)
  - left. econs. econs.
    + i. exploit transl_step_correct; eauto. i. des; esplits; eauto.
      { eapply tr_rel_refl. eapply ev_rel_refl. }
      left. split; eauto.
      { eapply plus_one; eauto. }
      { eapply CSSAD.semantics_receptive_at; auto. }
    + ii. eapply final_state_determ; eauto.
      inv FINALSRC. inv MATCH. inv STACK. econs.
  (* external *)
  - right. econs. i. econs.
    + i. exploit match_states_bsim; eauto. i. des.
      left. esplits; eauto.
      { eapply tr_rel_refl. eapply ev_rel_refl. }
      left. eapply plus_one. eauto.
    + ii. inv FINALTGT. inv MATCH. ss.
    + i.
      specialize (SAFESRC _ (star_refl _ _ _)). des; cycle 2; clarify.
      { inv SAFESRC; ss. }
      inv MATCH; ss; des_ifs;
      match goal with
      | [H : transl_fundef (Internal ?f) = _ |- _ ] => idtac
      | [H : transl_fundef (External ?f) = _ |- _ ] => idtac
      | [  |- context [RTLpar.Returnstate ?ts ?vres ?m]] => idtac
      | _ =>
          (exploit transl_function_charact; eauto; intros;
           exploit transl_function_correct; eauto; intros)
      end;
      match goal with
      | [SPEC: transl_function_spec ?f ?tf |- _ ] =>
          inv SPEC
      | _ => try (generalize (wf_cssa f) ; intros HWF)
      end.
      * exploit codeSome; eauto. i. inv SAFESRC; clarify.
        right. esplits.
        (* right. *) (* esplits.  *) eapply RTLpar.exec_Ibuiltin.
        { eauto. }
        { inv MREG.
          eqregreprs regrepr0 regrepr.
          assert (forall r, In r (params_of_builtin_args l) -> rs !! r = rs' !! (regrepr r)).
          { intros. apply H2.
            left. split; auto.
            (* properties of [r] *)
            eapply live_at_notinop_if_used; eauto.
            go. go.
            apply not_lazydef_outside_inop; go.          
          }
          eapply eval_builtin_args_preserved with (ge1:= ge).
          apply senv_preserved.
          instantiate (1:=vargs).
          revert H11 H3. clear.
          induction 1 ; intros; go.
          simpl. constructor.
          + clear H11 IHlist_forall2.
            revert H H3.
            induction 1 ; intros ; simpl ; go.
            * rewrite H3; go.
            * { constructor.
                - eapply IHeval_builtin_arg1; eauto.
                  intros. eapply H3; eauto. simpl in *.
                  eapply in_app_or in H1.
                  eapply in_or_app. intuition.
                - eapply IHeval_builtin_arg2; eauto.
                  intros. eapply H3; eauto. simpl in *.
                  eapply in_app_or in H1.
                  eapply in_or_app. intuition.
              }
            * { constructor.
                - eapply IHeval_builtin_arg1; eauto.
                  intros. eapply H3; eauto. simpl in *.
                  eapply in_app_or in H1.
                  eapply in_or_app. intuition.
                - eapply IHeval_builtin_arg2; eauto.
                  intros. eapply H3; eauto. simpl in *.
                  eapply in_app_or in H1.
                  eapply in_or_app. intuition.
              }
          + eapply IHlist_forall2; eauto.
            intros. eapply H3. go. }
        eapply  external_call_symbols_preserved; eauto. apply senv_preserved.
      * inv SPEC. inv SAFESRC; clarify.
        right. esplits.
        eapply RTLpar.exec_function_external.
        eapply external_call_symbols_preserved; eauto.
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
    (INITSRC: CSSA.initial_state prog S1)
    (INITTGT: RTLpar.initial_state tprog S2)
    (MATCH: match_init S1 S2)
    (CAPTGT: RTLpar.glob_capture tprog S2 S2'):
  exists S1',
    CSSA.glob_capture prog S1 S1'
  /\ match_states S1' S2'
  /\ gm_improves (CSSA.concrete_snapshot ge S1') (RTLpar.concrete_snapshot tge S2').
Proof.
  specialize senv_preserved. intros SENVEQ. inv CAPTGT. ss.
  rewrite Genv.globalenv_public in CAPTURE.
  rewrite <- same_public in CAPTURE. erewrite <- non_static_equiv in CAPTURE.
  inv MATCH. inv STACK.
  esplits.
  - econs; eauto. rewrite Genv.globalenv_public. eauto.
  - econs; eauto. r. esplits; eauto.
    { econs; eauto. rewrite Genv.globalenv_public. eauto. }
    eapply star_refl.
  - ii. unfold RTLpar.concrete_snapshot, CSSA.concrete_snapshot in *.
    inv SENVEQ. des. erewrite H1, H0. des_ifs; ss.
Qed.

Theorem transf_program_correct:
  mixed_simulation (CSSA.semantics prog) (RTLpar.semantics tprog).
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
      inv STACK.
      exploit transf_initial_capture; eauto.
      i. des.
      exists 0%nat. exists S1'. esplits; eauto.
      apply match_states_xsim; auto.
  - i. apply senv_preserved.
Qed.

  End CORRECTNESS.
  
End PRESERVATION.

Section WF.

Variable prog: CSSA.program.
Variable tprog: RTLpar.program.
Hypothesis TRANSF_PROG: match_prog prog tprog.
Hypothesis WF_TRANSF: wf_cssa_program prog. 

Lemma transl_function_inops : forall f tf, 
  transl_function f = Errors.OK tf -> 
  forall pc s, 
    (fn_code f) ! pc = Some (Inop s) <->
    (RTLpar.fn_code tf) ! pc = Some (Inop s).
Proof.
  unfold transl_function ; intros f tf TRANS pc s.
  flatten TRANS; simpl.
  unfold transl_code. rewrite PTree.gmap1.
  unfold option_map. 
  split.
  - intros INOP. rewrite INOP; auto.
  - flatten ; destruct i ; go ; try solve [simpl ; flatten].
Qed.

Lemma transl_function_ins : forall f tf, 
  transl_function f = Errors.OK tf -> 
  forall pc ins, 
    (fn_code f) ! pc = Some ins ->
    exists ins', (RTLpar.fn_code tf) ! pc = Some ins'.
Proof.
  unfold transl_function ; intros f tf TRANS pc ins INS.
  flatten TRANS; simpl.
  unfold transl_code. rewrite PTree.gmap1.
  unfold option_map. rewrite INS; auto.
  destruct ins ; go.
Qed.

Lemma transl_function_ins_2 : forall f tf, 
  transl_function f = Errors.OK tf -> 
  forall pc ins, 
    (RTLpar.fn_code tf) ! pc = Some ins ->
    exists ins', (fn_code f) ! pc = Some ins'. 
Proof.
  unfold transl_function ; intros f tf TRANS pc ins INS.
  flatten TRANS; simpl in *.
  unfold transl_code in *. rewrite PTree.gmap1 in *.
  unfold option_map in *. flatten INS ; eauto. 
Qed.

Lemma transl_function_parcb_2 : forall f tf, 
  transl_function f = Errors.OK tf -> 
  forall pc p, 
    (RTLpar.fn_parcopycode tf) ! pc = Some p ->
    exists p, (fn_parcopycode f) ! pc = Some p. 
Proof.
  unfold transl_function ; intros f tf TRANS pc ins INS.
  flatten TRANS; simpl in *.
  unfold parcopycode_cleanup, transl_parcopycode in *. 
  repeat rewrite PTree.gmap1 in *.
  unfold option_map in *. flatten INS ; eauto. 
Qed.

Lemma entry_point_preserved : 
  forall f tf,
  transl_function f = OK tf -> 
  RTLpar.fn_entrypoint tf = fn_entrypoint f.
Proof.
  unfold transl_function ; intros f tf TRANS.
  flatten TRANS; go.
Qed.

Lemma successors_preserved : forall f tf,
  transl_function f = Errors.OK tf -> 
  forall pc ins ins' pc', 
    (fn_code f) ! pc = Some ins ->
    (RTLpar.fn_code tf) ! pc = Some ins' ->
    (In pc' (successors_instr ins) <->
     In pc' (successors_instr ins')).
Proof.
  unfold transl_function ; intros f tf TRANS pc ins ins' pc' CODE TCODE.
  flatten TRANS; simpl in *; go.  
  unfold transl_code in *. rewrite PTree.gmap1 in *.
  unfold option_map in *. rewrite CODE in *.
  destruct ins ; go;
  try solve [destruct s0 ; go];
  destruct o ; go.
Qed.

Lemma successors_preserved_2 : forall f tf,
  transl_function f = Errors.OK tf -> 
  forall pc pc', In pc' (successors f) !!! pc <->
                 In pc' (RTLpar.successors tf) !!! pc.
Proof.
  intros f tf TRANS pc pc'.
  unfold successors, RTLpar.successors.
  unfold successors_list; simpl.
  repeat rewrite PTree.gmap1 in *.
  unfold option_map.
  flatten; simpl;  go ; flatten Eq0; eauto using successors_preserved ; eauto.
  - split; intuition; exploit transl_function_ins ; eauto.
    intros [ins' Hins']; congruence.
  - split; intuition; exploit transl_function_ins_2 ; eauto.
    intros [ins' Hins']; congruence.
Qed.

Lemma cfg_preserved : forall f tf,
  transl_function f = Errors.OK tf -> 
  forall pc pc', cfg f pc pc' <-> RTLpar.cfg tf pc pc'.
Proof.
  intros f tf TRANS pc pc'.
  split; intros.
  - invh cfg. 
    exploit transl_function_ins; eauto. 
    intros [ins' Hins']. 
    econstructor; eauto using successors_preserved. 
    eapply successors_preserved with (ins:= ins) ; go.
  - invh RTLpar.cfg. 
    exploit transl_function_ins_2; eauto. 
    intros [ins' Hins']. 
    econstructor; eauto using successors_preserved. 
    eapply successors_preserved with (ins:= ins') ; go.
Qed.

Lemma is_wf_function : forall f tf, 
  wf_cssa_function f ->                         
  transl_function f = Errors.OK tf -> 
  RTLpar.wf_function tf. 
Proof.
  intros. constructor.

  - exploit fn_entry; eauto. intros [s Hins].
    erewrite entry_point_preserved; eauto.
    rewrite transl_function_inops in Hins ; eauto. 

  - intros pc Hcont.
    invh RTLpar.cfg.
    unfold transl_function in *.
    flatten TRANS; simpl in *.
    unfold transl_code in *. rewrite PTree.gmap1 in HCFG_ins.
    unfold option_map in *. flatten HCFG_ins. 
    destruct i ; eelim fn_entry_pred; go; 
    try solve [simpl in *; flatten HCFG_ins; subst; eelim fn_entry_pred; go].

  - intros jp pc JP SUCC.
    erewrite <- successors_preserved_2 in SUCC; eauto.
    exploit fn_normalized ; eauto using jp_preserved_2.
    rewrite transl_function_inops; eauto.
    
  - intros pc pc' JP CFG JPCONT.
    eapply jp_preserved_2 in JP ; eauto. 
    eapply jp_preserved_2 in JPCONT ; eauto. 
    eelim wf_cssa_jp_not_jp with (pc:= pc) (pc':= pc') ; eauto.
    eapply cfg_preserved; eauto.

  - intros pc pc' parcb CODE TPARC NJP.
    eapply jp_preserved_1 ; eauto.
    rewrite <- transl_function_inops in *; eauto.
    exploit transl_function_parcb_2; eauto. intros [p Hp].
    eapply fn_parcbjp with (pc':= pc'); 
      eauto using jp_preserved_1.

  - intros pc PARC.
    destruct ((RTLpar.fn_parcopycode tf) ! pc) eqn: EQ; try congruence.
    exploit transl_function_parcb_2; go. intros [p' Hp'].
    exploit (CSSA.parcb_inop f H pc)  ; eauto; go. intros [s Hpc].
    rewrite transl_function_inops in Hpc; eauto.

  - intros pc pc' instr CODE SUCC.
    exploit transl_function_ins_2; eauto. intros [ins' CODE'].
    rewrite <- successors_preserved with (ins':= instr) in SUCC; eauto.
    exploit fn_code_closed; eauto. intros [instr' CODESUCC].
    exploit transl_function_ins; eauto.

Unshelve. 
go. go. go. go.
go. go. go. go.
go. go. go. 
Qed.

Theorem is_wf_program : RTLpar.wf_program tprog.
Proof.
  red. intros.
  red in  WF_TRANSF.
  inv TRANSF_PROG.
  intuition. revert H0 H WF_TRANSF. clear.
  generalize (prog_defs tprog).
  induction 1; intros.
  - inv H.
  - inv H1.      
    + inv H. inv H2.
      { destruct f1 ; simpl in * ; try constructor; auto.
        * monadInv H5.
          constructor.
          eapply is_wf_function; eauto.
          destruct a1, g.
          exploit (WF_TRANSF (Internal f0) i); eauto.
          simpl in * ; eauto.
          left. inv H; simpl in *; auto. 
          intros. inv H1; auto.
          simpl in *. inv H.
        * monadInv H5.
          constructor.
      }
    + eapply IHlist_forall2; eauto.
Qed.
 
End WF.
