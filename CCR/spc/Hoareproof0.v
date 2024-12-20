Require Import ProofMode.
Require Import CoqlibCCR.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef.
Require Import SimSTS.
Require Import SimGlobal.
From Ordinal Require Import Ordinal Arithmetic.
Require Import List.
Require Import Red IRed.


Set Implicit Arguments.

Local Open Scope nat.

















Module TAC.
  Ltac _step :=
    match goal with
    (*** terminal cases ***)
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (triggerUB >>= _) _ ] =>
      unfold triggerUB; mred; _step; ss; fail
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (triggerNB >>= _) ] =>
      unfold triggerNB; mred; _step; ss; fail
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (triggerNB >>= _) _ ] =>
      exfalso
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (triggerUB >>= _) ] =>
      exfalso

    (*** assume/guarantee ***)
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (assume ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (assume ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar

    (*** default cases ***)
    | _ =>
      (guclo simg_indC_spec; econs; eauto; try (by ss);
       (*** some post-processing ***)
       i;
       try match goal with
           | [ |- (eq ==> _)%signature _ _ ] =>
             let v_src := fresh "v_src" in
             let v_tgt := fresh "v_tgt" in
             intros v_src v_tgt ?; subst v_tgt
           end)
    end
  .
  Ltac seal_left :=
    match goal with
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ ?i_src ?i_tgt ] => seal i_src
    end.
  Ltac seal_right :=
    match goal with
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ ?i_src ?i_tgt ] => seal i_tgt
    end.
  Ltac unseal_left :=
    match goal with
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (@Seal.sealing _ _ ?i_src) ?i_tgt ] => unseal i_src
    end.
  Ltac unseal_right :=
    match goal with
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ ?i_src (@Seal.sealing _ _ ?i_tgt) ] => unseal i_tgt
    end.
  Ltac force_l := seal_right; _step; unseal_right.
  Ltac force_r := seal_left; _step; unseal_left.
  Ltac deflag := eapply simg_progress_flag.
  (* Ltac mstep := gstep; econs; eauto; [eapply from_nat_lt; ss|]. *)
End TAC.
Import TAC.


Section CANCEL.

  (*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
  Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)



  Context `{SK: Sk.ld}.
  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.

  Let sk: Sk.t := Sk.canon (fold_right Sk.add Sk.unit (List.map SMod.sk mds)).
  (* Let skenv: SkEnv.t := Sk.load_skenv sk. *)

  Let _mss: Sk.t -> list SModSem.t := fun sk => (List.map ((flip SMod.get_modsem) sk) mds).
  Let _sbtb: Sk.t -> list (gname * fspecbody) := fun sk => (List.flat_map (SModSem.fnsems) (_mss sk)).
  Let _stb: Sk.t -> list (gname * fspec) := fun sk => List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) (_sbtb sk).

  Let mss: list SModSem.t := _mss sk.
  Let sbtb: list (gname * fspecbody) := _sbtb sk.

  Variable stb: Sk.t -> gname -> option fspec.
  Hypothesis STBCOMPLETE:
    forall fn fsp (FIND: alist_find fn (_stb sk) = Some fsp), stb sk fn = Some fsp.
  Hypothesis STBSOUND:
    forall fn (FIND: alist_find fn (_stb sk) = None),
      (<<NONE: stb sk fn = None>>) \/ (exists fsp, <<FIND: stb sk fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>).

  (* Let mss: list SModSem.t := (List.map ((flip SMod.get_modsem) sk) mds). *)
  (* Let sbtb: list (gname * fspecbody) := (List.flat_map (SModSem.fnsems) mss). *)
  (* Let stb: list (gname * fspec) := List.map (fun '(fn, fs) => (fn, fs.(fsb_fspec))) sbtb. *)

  Let mds_mid: list Mod.t := List.map (SMod.to_mid (stb sk)) mds.
  Let mds_tgt: list Mod.t := List.map (SMod.to_tgt stb) mds.

  Let ms_mid: ModSemL.t := ModL.enclose (Mod.add_list mds_mid).
  Let ms_tgt: ModSemL.t := ModL.enclose (Mod.add_list mds_tgt).


  Lemma sk_eq:
    ModL.sk (Mod.add_list mds_tgt) = ModL.sk (Mod.add_list mds_mid).
  Proof.
    unfold ms_tgt, ms_mid, mds_mid, mds_tgt, ModL.enclose.
    rewrite ! Mod.add_list_sk. f_equal.
    generalize mds. clear. i. induction mds0; ss.
    rewrite IHmds0. auto.
  Qed.

  Lemma fst_initial_mrs_eq:
    List.map fst (ModSemL.initial_mrs ms_tgt) = List.map fst (ModSemL.initial_mrs ms_mid).
  Proof.
    pose proof sk_eq.
    unfold ms_tgt, ms_mid, mds_tgt, mds_mid, ModL.enclose.
    unfold mds_mid, mds_tgt in H. rewrite H.
    generalize (ModL.sk (Mod.add_list (List.map (SMod.to_mid (stb sk)) mds))). i.
    rewrite ! Mod.add_list_initial_mrs.
    generalize mds. clear. i. induction mds0; auto.
    ss. rewrite IHmds0. auto.
  Qed.

  Lemma fns_eq:
    (List.map fst (ModSemL.fnsems (ModL.enclose (Mod.add_list mds_tgt))))
    =
    (List.map fst (ModSemL.fnsems (ModL.enclose (Mod.add_list mds_mid)))).
  Proof.
    pose proof sk_eq. unfold ModL.enclose.
    unfold mds_mid, mds_tgt, ModL.enclose.
    unfold mds_mid, mds_tgt in H. rewrite H.
    generalize (ModL.sk (Mod.add_list (List.map (SMod.to_mid (stb sk)) mds))). i.
    rewrite ! Mod.add_list_fns. rewrite ! List.map_map. f_equal.
    f_equal. extensionality sm. ss. rewrite ! List.map_map. f_equal.
    extensionality fnsb. destruct fnsb as [fn sb]. ss.
  Qed.

  Lemma stb_find_iff_aux fn
    :
      ((<<NONE: alist_find fn (_stb sk) = None>>) /\
       (<<FINDMID: alist_find fn (ModSemL.fnsems ms_mid) = None>>) /\
       (<<FINDTGT: alist_find fn (ModSemL.fnsems ms_tgt) = None>>)) \/

      (exists md (f: fspecbody),
          (<<STB: alist_find fn (_stb sk) = Some (f: fspec)>>) /\
          (<<SBTB: alist_find fn sbtb = Some f>>) /\
          (<<FINDMID: alist_find fn (ModSemL.fnsems ms_mid) =
                      Some (transl_all (T:=_)
                              (SModSem.mn (SMod.get_modsem md sk))
                              ∘ fun_to_mid (stb sk) (fsb_body f))>>) /\
          (<<FINDTGT: alist_find fn (ModSemL.fnsems ms_tgt) =
                      Some (transl_all (T:=_)
                              (SModSem.mn (SMod.get_modsem md sk))
                              ∘ fun_to_tgt (SModSem.mn (SMod.get_modsem md sk)) (stb sk) f)>>) /\
          (<<MIN: List.In (SModSem.mn (SMod.get_modsem md sk)) (List.map fst ms_tgt.(ModSemL.initial_mrs))>>)).
  Proof.
    unfold ms_mid, ms_tgt, mds_tgt, mds_mid, SMod.to_mid, mds_tgt, SMod.to_tgt.
    rewrite SMod.transl_fnsems. rewrite SMod.transl_fnsems. rewrite SMod.transl_initial_mrs. fold sk.
    unfold _stb at 1 2. unfold sbtb, _sbtb, _mss. rewrite alist_find_map.
    generalize mds. induction mds0; ss; auto. rewrite ! alist_find_app_o.
    erewrite ! SMod.red_do_ret2. rewrite ! alist_find_map. uo.
    destruct (alist_find fn (SModSem.fnsems (SMod.get_modsem a sk))) eqn:FIND.
    { right. esplits; et. }
    des.
    { left. esplits; et. }
    { right. esplits; et. }
  Qed.

  Lemma stb_find_iff fn
    :
      ((<<NONE: stb sk fn = None>> \/ (exists fsp, <<FIND: stb sk fn = Some fsp>> /\ <<TRIVIAL: forall x, fsp.(measure) x = ord_top>>)) /\
       (<<FINDMID: alist_find fn (ModSemL.fnsems ms_mid) = None>>) /\
       (<<FINDTGT: alist_find fn (ModSemL.fnsems ms_tgt) = None>>)) \/

      (exists md (f: fspecbody),
          (<<STB: stb sk fn = Some (f: fspec)>>) /\
          (<<SBTB: alist_find fn sbtb = Some f>>) /\
          (<<FINDMID: alist_find fn (ModSemL.fnsems ms_mid) =
                      Some (transl_all (T:=_)
                              (SModSem.mn (SMod.get_modsem md sk))
                              ∘ fun_to_mid (stb sk) (fsb_body f))>>) /\
          (<<FINDTGT: alist_find fn (ModSemL.fnsems ms_tgt) =
                      Some (transl_all (T:=_)
                              (SModSem.mn (SMod.get_modsem md sk))
                              ∘ fun_to_tgt (SModSem.mn (SMod.get_modsem md sk)) (stb sk) f)>>) /\
          (<<MIN: List.In (SModSem.mn (SMod.get_modsem md sk)) (List.map fst ms_tgt.(ModSemL.initial_mrs))>>)).
  Proof.
    hexploit (stb_find_iff_aux fn). i. des.
    { left. esplits; et. }
    { right. esplits; et. }
  Qed.

  Let W: Type := (p_state).

  Let r_state: Type := mname -> Σ.

  Let zip_state (mps: p_state) (mrs: r_state): p_state :=
    fun mn => match alist_find mn ms_tgt.(ModSemL.initial_mrs) with
              | Some r => Any.pair (mps mn) (mrs mn)↑
              | None => mps mn
              end.

  Let rsum_minus (mn: mname): r_state -> Σ :=
    fun mrs_tgt => (fold_left (⋅) (List.map (update mrs_tgt mn ε) (List.map fst ms_tgt.(ModSemL.initial_mrs))) ε).

  Let rsum: r_state -> Σ :=
    fun mrs_tgt => (fold_left (⋅) (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε).



  Lemma fold_left_add (r: Σ) rs
    :
      fold_left URA.add rs r = (fold_left URA.add rs ε) ⋅ r.
  Proof.
    revert r. induction rs; ss.
    { i. rewrite URA.unit_idl. auto. }
    i. rewrite IHrs. rewrite (IHrs (ε ⋅ a)). r_solve.
  Qed.

  Let rsum_update mn (mrs: r_state) r (mns: list mname) r0
      (MIN: List.In mn mns)
      (NODUP: NoDup mns)
    :
      (fold_left (⋅) (List.map (update mrs mn r) mns) r0) ⋅ (mrs mn)
      =
      (fold_left (⋅) (List.map mrs mns) r0) ⋅ r.
  Proof.
    revert mn mrs r r0 MIN NODUP. induction mns; ss. i.
    inv NODUP. des.
    { subst. rewrite fold_left_add. rewrite (fold_left_add (r0 ⋅ mrs mn)).
      rewrite <- ! URA.add_assoc. f_equal.
      { f_equal. apply map_ext_in. i.
        unfold update. des_ifs. }
      { unfold update. des_ifs. r_solve. }
    }
    { rewrite IHmns; et.
      rewrite fold_left_add. rewrite (fold_left_add (r0 ⋅ mrs a)).
      unfold update. des_ifs. }
  Qed.

  Lemma rsum_minus_update mn0 mn1 mrs r
        (MIN0: List.In mn0 (List.map fst ms_tgt.(ModSemL.initial_mrs)))
        (MIN1: List.In mn1 (List.map fst ms_tgt.(ModSemL.initial_mrs)))
        (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      rsum_minus mn0 mrs ⋅ r = rsum_minus mn1 (update mrs mn0 r) ⋅ update mrs mn0 r mn1.
  Proof.
    unfold rsum_minus.
    revert MIN0 MIN1 NODUP. generalize (List.map fst (ModSemL.initial_mrs ms_tgt)). i.
    rewrite rsum_update; et.
    transitivity (fold_left (⋅) (List.map (update (update mrs mn0 ε) mn0 r) l) ε ⋅ (update mrs mn0 ε mn0)).
    { rewrite rsum_update; et. }
    { f_equal.
      { f_equal. f_equal. extensionality mn. unfold update. des_ifs. }
      { unfold update. des_ifs. }
    }
  Qed.

  Lemma rsum_minus_rsum mn mrs
        (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs)))
        (IN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      rsum_minus mn mrs ⋅ mrs mn = rsum mrs.
  Proof.
    unfold rsum_minus, rsum. revert NODUP IN.
    setoid_rewrite <- (List.map_map fst mrs).
    generalize (map fst (ModSemL.initial_mrs ms_tgt)) as mns.
    i. rewrite rsum_update; et. r_solve.
  Qed.

  Lemma initial_mrs_exist
        (NODUP: List.NoDup (map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      exists (initial_mrs: r_state),
        (<<INITIALZIP:
           zip_state (ModSemL.initial_p_state ms_mid) initial_mrs =
           ModSemL.initial_p_state ms_tgt>>) /\
        (<<INITIALRSUM:
           forall mn (MIN: List.In mn (map fst ms_tgt.(ModSemL.initial_mrs))),
             rsum_minus mn initial_mrs ⋅ initial_mrs mn = fold_left URA.add (List.map SModSem.initial_mr mss) ε>>).
  Proof.
    exists (fun mn =>
              match alist_find mn (SMod.load_initial_mrs
                                     (Sk.canon (foldr Sk.add Sk.unit (map SMod.sk mds))) mds
                                     SModSem.initial_mr) with
              | Some r => r
              | _ => ε
              end).
    split.
    { revert NODUP.
      unfold ModSemL.initial_p_state, zip_state.
      unfold ms_mid, ms_tgt.
      unfold mds_mid, mds_tgt, SMod.to_mid, SMod.to_tgt. ss.
      rewrite ! SMod.transl_initial_mrs.
      generalize (Sk.canon (fold_right Sk.add Sk.unit (map SMod.sk mds))).
      intros sk0. i. red. extensionality mn.
      unfold SMod.load_initial_mrs.
      rewrite ! SMod.red_do_ret. clear. induction mds; ss.
      rewrite ! eq_rel_dec_correct. des_ifs.
    }
    { ii. rewrite rsum_minus_rsum; et. fold sk. unfold rsum. clear mn MIN.
      f_equal. revert NODUP.
      unfold mss, _mss, ms_tgt, mds_tgt, SMod.to_tgt.
      rewrite ! SMod.transl_initial_mrs.
      unfold SMod.load_initial_mrs.
      rewrite ! SMod.red_do_ret.
      rewrite ! List.map_map. ss. fold sk. generalize sk. clear. i.
      eapply map_ext_in. i. des_ifs.
      { eapply alist_find_some in Heq.
        eapply in_map_iff in Heq. des. clarify.
        destruct (classic (a = x)).
        { subst. auto. }
        eapply NoDup_inj_aux in H0; et. ss.
        exfalso. eapply H0. et.
      }
      { exfalso. eapply alist_find_none in Heq.
        eapply (in_map (fun x => (SModSem.mn (SMod.get_modsem x sk), SModSem.initial_mr (SMod.get_modsem x sk)))) in H; et.
      }
    }
  Qed.

  Local Opaque rsum rsum_minus.


  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac mred := repeat (cbn; ired_both).

  Ltac steps := repeat (mred; try _step; des_ifs_safe).


  Let zip_state_get st mrs mn
      (MIN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      zip_state st mrs mn = Any.pair (st mn) (mrs mn)↑.
  Proof.
    unfold zip_state. des_ifs.
    eapply in_map_iff in MIN. des. destruct x. subst.
    eapply alist_find_none in Heq.
    exfalso. eapply Heq. et.
  Qed.

  Let zip_state_mput st mrs mn r
      (MIN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      update (zip_state st mrs) mn (Any.pair (st mn) (Any.upcast r))
      =
      zip_state st (update mrs mn r).
  Proof.
    extensionality mn0.
    unfold update, zip_state. des_ifs.
    eapply in_map_iff in MIN. des. destruct x. subst.
    eapply alist_find_none in Heq.
    exfalso. eapply Heq. et.
  Qed.


  Let adequacy_type_aux
      (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs))):
    forall RT
           mrs0 frs ctx0
           st_src0 st_tgt0 (i0: itree (hCallE +' pE +' eventE) RT)
           mn cur
           (ZIP: st_tgt0 = zip_state st_src0 mrs0)
           (CTX: ctx0 = frs ⋅ rsum_minus mn mrs0)

           (MIN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
           (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    ,
      simg (fun '(st_src1, v_src) '(st_tgt1, v_tgt) =>
              exists mrs1,
                (<<ZIP: st_tgt1 = zip_state st_src1 mrs1>>) /\
                (<<RET: (v_tgt: Σ * RT) = (frs ⋅ rsum_minus mn mrs1, v_src)>>))
           false false
           (EventsL.interp_Es (ModSemL.prog ms_mid) (transl_all mn (interp_hCallE_mid (stb sk) cur i0)) st_src0)
           (EventsL.interp_Es (ModSemL.prog ms_tgt) (transl_all mn (interp_hCallE_tgt mn (stb sk) cur i0 ctx0)) st_tgt0)
  .
  Proof.
    Opaque subevent.
    ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    gcofix CIH. i; subst.
    ides i0; try rewrite ! unfold_interp; cbn; mred.
    { steps. }
    { steps. deflag. gbase. eapply CIH; [..|M]; Mskip et. ss. }
    rewrite <- bind_trigger. destruct e; cycle 1.
    {
      destruct s; ss.
      {
        destruct p; ss.
        - resub. steps.
          erewrite zip_state_get; et. steps. deflag.
          gbase. eapply CIH; ss.
          extensionality mn0. unfold update, zip_state. des_ifs.
          exfalso. eapply in_map_iff in MIN. des. destruct x. subst.
          eapply alist_find_none in Heq. et.
        - resub. steps.
          erewrite zip_state_get; et. steps. deflag.
          gbase. eapply CIH; ss.
      }
      { dependent destruction e.
        - resub. ired_both. force_r. steps. esplits; eauto. steps. deflag.
          gbase. eapply CIH; [..|M]; Mskip et. ss.
        - resub. steps. esplits; eauto. steps. deflag. gbase. eapply CIH; [..|M]; Mskip et. ss.
        - resub. steps. deflag. gbase. eapply CIH; [..|M]; Mskip et. ss.
      }
    }
    dependent destruction h. resub.
    set (ModSemL.prog ms_mid) as p_mid in *.
    set (ModSemL.prog ms_tgt) as p_tgt in *.
    ss.
    seal_left.

    steps. hexploit (stb_find_iff fn). i. des.
    { rewrite NONE. steps. }
    { rewrite FIND. unfold HoareCall, ASSUME, ASSERT, mput, mget. steps.
      erewrite zip_state_get; et. steps.
      des; clarify. destruct tbr; ss.
      { exfalso. hexploit TRIVIAL; et. intro T. rewrite T in *. hexploit x4; ss. }
      seal_right. unseal_left. steps. rewrite FIND. steps. esplits; et.
      steps. esplits; et.
      { destruct cur; ss. hexploit x5; ss. intro T. rewrite T in *; ss. }
      steps. rewrite FINDMID. steps.
    }
    unfold HoareCall, ASSUME, ASSERT, mput, mget.

    (*** exploiting both_tau ***)
    rewrite STB. ss. mred. force_r.
    destruct (classic (tbr = true /\ forall x, f.(measure) x = ord_top)).
    { des. subst. steps.
      erewrite zip_state_get; et. rewrite Any.pair_split. steps.
      hexploit H0; et. i. rewrite H in *. ss. des. hexploit x4; ss. }
    rename H into TRIVIAL.
    unseal_left. ired_both. rewrite STB. steps. esplit.
    { ii. subst. eapply TRIVIAL; ss. } steps.
    erewrite zip_state_get; et. rewrite Any.pair_split. steps.

    match goal with
    | |- _ ?i_tgt => replace i_tgt with (Ret tt;;; i_tgt)
    end.
    2: { mred. auto. }
    deflag. guclo bindC_spec. econs.
    { instantiate (1:= fun '(st_src, o) (_: unit) => st_src = st_src0 /\ o = (f.(measure) x)).
      destruct tbr.
      { steps. des. destruct (measure f x); ss.
        { exists n. steps. }
        { exfalso. hexploit x4; ss. }
      }
      { steps. des. splits; auto. symmetry. auto. }
    }
    i. destruct vret_src, vret_tgt. des; subst.

    steps. esplits; eauto. steps. unfold unwrapU.
    rewrite FINDMID. rewrite FINDTGT. rewrite ! bind_ret_l.

    guclo bindC_spec. econs.

    { instantiate (1:= fun '(st_src1, vret_src) '(st_tgt1, vret_tgt) =>
                         exists (mrs1: r_state) rret,
                           (<<ZIP: st_tgt1 = zip_state st_src1 mrs1>>) /\
                           (<<POST: f.(postcond) (Some mn) x vret_src vret_tgt rret>>) /\
                           (<<RWF: URA.wf (rret ⋅ (c1 ⋅ (frs ⋅ rsum_minus mn mrs1) ⋅ (mrs1 mn)))>>)).
      fold sk. fold sk. set (mn0:=SModSem.mn (SMod.get_modsem md sk)) in *.
      fold Any_tgt in x3.
      unfold fun_to_src, fun_to_tgt, compose. des_ifs. unfold HoareFun, ASSUME, ASSERT, mget, mput.
      rename x3 into PRECOND. rename c0 into rarg.
      steps. exists x.
      steps. eexists (rarg, c1 ⋅ (frs ⋅ rsum_minus mn0 (update mrs0 mn c))). steps.
      erewrite ! zip_state_mput; et. steps.
      erewrite zip_state_get; et. steps.
      assert (RWF0: URA.wf (rarg ⋅ ε ⋅ (c1 ⋅ (frs ⋅ rsum_minus mn0 (update mrs0 mn c))) ⋅ update mrs0 mn c mn0)).
      { r_wf x0. symmetry. eapply rsum_minus_update; et. }
      unshelve esplits; eauto. steps.
      exists varg_src.
      steps. esplits; eauto. steps. unshelve esplits; eauto. steps.
      deflag. guclo bindC_spec. econs.
      { gbase. eapply CIH; ss.
        { instantiate (1:=c1 ⋅ frs). r_solve. }
      }
      { ii. ss. des_ifs_safe. des; ss. clarify.
        steps. rewrite zip_state_get; et.
        rewrite Any.pair_split. steps.
        esplits; ss; et.
        { assert(URA.wf (c2 ⋅ (c1 ⋅ frs ⋅ rsum_minus mn0 mrs1) ⋅ c0)).
          { eapply (@URA.wf_mon _ _ c3). r_wf x3. }
          r_wf H. symmetry. eapply rsum_minus_update; et. }
      }
    }
    { ii. ss. des_ifs_safe. des. subst.
      steps. eexists (rret, frs ⋅ rsum_minus mn mrs1). steps.
      rewrite zip_state_get; et.
      rewrite Any.pair_split. steps. rewrite Any.upcast_downcast. steps.
      unshelve esplits; et.
      { r_wf RWF. }
      steps. exists t. steps. unshelve esplits; et.
      steps. deflag. gbase. eapply CIH; et.
    }
  Unshelve.
    all: try (by exact 0).
  Qed.

  Opaque EventsL.interp_Es.

  Context {CONFS: EMSConfig}.
  Definition midConf: EMSConfig := {| finalize := finalize; initial_arg := Any.pair ord_top↑ initial_arg |}.
  Context {CONFT: EMSConfig}.
  Hypothesis (FINSAME: (@finalize CONFS) = (@finalize CONFT)).

  Theorem adequacy_type_t2m
          (MAINM:
             forall (main_fsp: fspec) (MAIN: stb sk "main" = Some main_fsp),
             exists (x: main_fsp.(meta)) entry_r,
               (<<PRE: main_fsp.(precond) None x (@initial_arg CONFS) (@initial_arg CONFT) entry_r ∧ main_fsp.(measure) x = ord_top>>) /\
               (<<WFR: URA.wf (entry_r ⋅ fold_left (⋅) (List.map SModSem.initial_mr mss) ε)>>) /\
               (<<RET: forall ret_src ret_tgt r
                              (WFR: URA.wf r)
                              (POST: main_fsp.(postcond) None x ret_src ret_tgt r),
                   ret_src = ret_tgt>>)):
    Beh.of_program (@ModL.compile _ CONFT (Mod.add_list mds_tgt)) <1=
    Beh.of_program (@ModL.compile _ midConf (Mod.add_list mds_mid)).
  Proof.
    eapply adequacy_global_itree; ss.
    ginit.
    { eapply cpn7_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr, ModSemL.initial_itr. Local Opaque ModSemL.prog. ss.
    unfold ITree.map.

    hexploit (stb_find_iff "main"). i. destruct H as [[_ ?]|?]; des; clarify.
    { Local Transparent ModSemL.prog.
      seal_right. ss. unfold ms_mid in FINDMID. rewrite FINDMID. 
      unfold ModL.wf_bool. destruct ModL.wf_dec; ss; steps.
      Local Opaque ModSemL.prog. }
    rename f into main_fsb. hexploit MAINM; et.
    i. des.

    unfold ModL.wf_bool. destruct ModL.wf_dec; ss; steps.
    unfold ModL.wf in *. des.
    assert (NODUP: List.NoDup (map fst ms_tgt.(ModSemL.initial_mrs))).
    { inv WF. rewrite fst_initial_mrs_eq. unfold ms_mid. auto. }
    destruct ModL.wf_dec; ss; [|exfalso; apply n; econs]; cycle 1.
    { inv WF. econs; auto. rewrite fns_eq. auto. }
    { rewrite sk_eq. auto. }

    hexploit initial_mrs_exist; auto. i. des.
    steps. fold ms_tgt ms_mid. rewrite <- INITIALZIP.

    Local Transparent ModSemL.prog. ss.
    unfold Any_src, Any_mid, Any_tgt in *. rewrite FINDTGT. rewrite FINDMID. steps.
    eexists. steps. unfold ASSUME, ASSERT, mput, mget. steps.
    eexists (entry_r, rsum_minus (SModSem.mn (SMod.get_modsem md sk)) initial_mrs).
    steps. rewrite zip_state_get; et. steps.
    assert (RWF: URA.wf (entry_r ⋅ ε ⋅ rsum_minus (SModSem.mn (SMod.get_modsem md sk)) initial_mrs ⋅ initial_mrs (SModSem.mn (SMod.get_modsem md sk)))).
    { r_wf WFR. eapply INITIALRSUM; et. }
    unshelve esplits; et.
    steps.
    eexists. steps. unshelve esplits; et. steps.
    guclo bindC_spec. econs.
    { apply simg_flag_down. gfinal. right. fold simg.
      eapply adequacy_type_aux; ss.
      { r_solve. }
    }
    i. ss.
    destruct vret_src as [mps_src v_src].
    destruct vret_tgt as [mps_tgt [? v_tgt]]. des. clarify.
    steps. rewrite zip_state_get; et.
    rewrite Any.pair_split. steps.
    { eapply RET; [|et]. eapply URA.wf_mon.
      instantiate (1:=(c1 ⋅ ε ⋅ rsum_minus (SModSem.mn (SMod.get_modsem md sk)) mrs1) ⋅ c).
      r_wf x0. }
    Unshelve. all: try (exact 0).
  Qed.

End CANCEL.