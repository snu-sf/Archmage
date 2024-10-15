(** This file contains the proof that the implementation of the
    validator satisfies its specification (see file
    [SSAvalidspec]). *)

Require Import Coq.Unicode.Utf8.
Require Import Axioms.
Require Import Classical.
Require Recdef.
Require Import FSets.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import Conventions. 
Require Import Kildall.
Require Import KildallComp.
Require Import Utils.
Require Import RTLdfs.
Require Import RTLutils.
Require RTLdfsgen.
Require Import SSA.
Require Import SSAutils.
Require Import SSAvalid.  
Require Import Utilsvalidproof.
Require Import SSAvalidprop.
Require Import LightLive.
Require Import SSAvalidspec.
Require Import Bijection.
Require Import sflib.

(** * The checkers [check_valid_index] and [check_valid_index_phis] are correct *)
Lemma check_valid_index_correct : forall size def,
    check_valid_index size def = true ->
    forall pc i, def ! pc = Some i -> Bij.valid_index size i = true.
Proof.
  unfold check_valid_index.
  intros ? ? CHECK ? ? DEF.
  eapply forall_ptree_true in CHECK; eauto.
Qed.

Lemma check_valid_index_phis_correct : forall size phi_def,
    check_valid_index_phis size phi_def = true ->
    forall pc phi, phi_def ! pc = Some phi ->
                   forall r i, phi ! r = Some i -> Bij.valid_index size i = true.
Proof.
  unfold check_valid_index_phis.
  intros ? ? CHECK ? ? PHI ? ? DEF.
  eapply forall_ptree_true in CHECK; eauto.
  eapply forall_ptree_true in CHECK; eauto.
Qed.
  
(** * The checker [check_function_inv] satisfies its specification *)
Lemma check_function_inv_correct0 : forall (f: RTLdfs.function), 
  check_function_inv f (make_predecessors (RTLdfs.fn_code f) RTL.successors_instr) = true -> 
  forall pc pc' instr , (RTLdfs.fn_code f) ! pc = Some instr ->
    In pc' (RTL.successors_instr instr) -> 
    exists instr', (RTLdfs.fn_code f) ! pc' = Some instr'.
Proof.
  intros tf  CHECK pc  pc' instr Hinstr Hsuccs.
  unfold check_function_inv in *.
  case_eq ((RTLdfs.fn_code tf) ! (RTLdfs.fn_entrypoint tf)); intros; rewrite H in *. 
  destruct i ; boolInv; try congruence. 
  eapply ptree_forall with (i := pc) in H1; eauto. 
  unfold check_instr_inv in H1. rewrite Hinstr in *. boolInv.
  set (f := (fun (i : positive) => match (RTLdfs.fn_code tf) ! i with
                                     | Some _ => true
                                     | None => false
                                   end)) in *.
  exploit (list_forall f) ; eauto. 
  unfold f in *.
  case_eq ((RTLdfs.fn_code tf) ! pc') ; intros; eauto.
  rewrite H4 in *; congruence. inv CHECK.
Qed.
  
Lemma check_function_inv_correct01 : forall (f: RTLdfs.function), 
  check_function_inv f (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) = true -> 
  forall i ins, 
    (RTLdfs.fn_code f)!i = Some ins ->
    In (RTLdfs.fn_entrypoint f) (RTLdfs.successors_instr ins) -> False.
Proof.
  intros f CHECK pc ins Hpc1 Hcont. 
  unfold check_function_inv in *.
  case_eq ((RTLdfs.fn_code f) ! (RTLdfs.fn_entrypoint f)); [intros i Hi | intros Hi] ; rewrite Hi in *.
  - destruct i ; try congruence.
    unfold no_pred in *.
    boolInv. clear H0.
    case_eq ((make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) !!! (RTLdfs.fn_entrypoint f));
      [intros Hpreds | intros p l Hpreds]; rewrite Hpreds in *. 
    * clear Hi.
      exploit @make_predecessors_correct_1; eauto. 
      intros Hcont'. rewrite Hpreds in Hcont'. inv Hcont'.
    * congruence. 
  - congruence.
Qed.

Lemma check_function_inv_correct11 : forall (f: RTLdfs.function), 
  check_function_inv f (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) = true -> 
  (exists instr, (RTLdfs.fn_code f) ! (RTLdfs.fn_entrypoint f) = Some instr).
Proof.
  intros tf  CHECK. 
  unfold check_function_inv in *.
  case_eq ((RTLdfs.fn_code tf) ! (RTLdfs.fn_entrypoint tf)); intros; eauto.
  rewrite H in *. inv CHECK.
Qed.

Lemma check_function_inv_correct12 : forall (f: RTLdfs.function), 
  check_function_inv f (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) = true -> 
  ~ RTLutils.join_point (RTLdfs.fn_entrypoint f) f.
Proof.
  intros tf  CHECK. 
  generalize (check_function_inv_correct11 tf CHECK) ; intros.
  destruct H.
  intro Hjp.
  inv Hjp. 
  
  unfold check_function_inv in *.
  rewrite H in *.
  destruct x ; try congruence ; boolInv.
  rename H1 into CHECK.
  eapply ptree_forall with (i := RTLdfs.fn_entrypoint tf) in CHECK; eauto. 
  unfold check_instr_inv in CHECK. 
  rewrite peq_true in *.
  boolInv.
  rewrite Hpreds in *.
  destruct l; simpl in *; try lia.
  destruct l; simpl in *; try lia.
  congruence.
Qed.

Lemma check_function_inv_correct3 : forall f: RTLdfs.function, 
  check_function_inv f (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) = true -> 
  (forall jp pc i,
    RTLutils.join_point jp f -> In jp (RTLdfs.successors_map f) !!! pc ->
    (RTLdfs.fn_code f) ! jp = Some i ->
    (RTLdfs.fn_code f) ! pc = Some (RTL.Inop jp)).  
Proof.
  intros tf CHECK jp pc i Hjp Hinsuccpc Hi.
  generalize Hjp; intros.
  inv Hjp0. 

  generalize CHECK ; intros CHECK'.
  unfold check_function_inv in CHECK'.
  exploit check_function_inv_correct11 ; eauto. intros [instr Hinstr]. 
  rewrite Hinstr in *. allinv. 
  destruct instr ; try congruence.
  boolInv. 
  rename H0 into CHECK'.
  eapply ptree_forall with (i := jp) in CHECK'; eauto. 
  unfold check_instr_inv in CHECK'.
  
  rewrite Hi in *.  rewrite Hpreds in *. 
  destruct (peq (RTLdfs.fn_entrypoint tf) jp).
  - boolInv. 
    destruct l; simpl in *; try (apply False_ind; lia).
    destruct l; simpl in *; try (apply False_ind; lia).
    congruence.
    
  - boolInv.
    
    destruct l. congruence. 
    destruct l. simpl in *. lia.

    assert (In pc ((make_predecessors (RTLdfs.fn_code tf) RTLdfs.successors_instr)!!! jp)).
    { 
      unfold RTLdfs.successors_map, successors_list in Hinsuccpc.      
      rewrite PTree.gmap1 in Hinsuccpc.
      case_eq (option_map RTLdfs.successors_instr (RTLdfs.fn_code tf) ! pc) ; intros.
      exploit option_map_some; eauto. intros [ipc Hipc]. 
      eapply make_predecessors_correct_1 with (n1:= pc); eauto.
      unfold option_map in *.
      rewrite Hipc in *. inv H1. auto.
      
      unfold option_map in *.
      case_eq ((RTLdfs.fn_code tf) ! pc) ; intros; rewrite H3 in *. 
      congruence.
      inv Hinsuccpc.
    }      

    unfold successors_list in *.
    rewrite Hpreds in *.
    unfold RTLdfs.successors_map in *.
    rewrite PTree.gmap1 in Hinsuccpc.
    unfold option_map in Hinsuccpc. 

    exploit @make_predecessors_some; eauto.
    intros [ipc Hipc]. 
    eapply list_forall in H1; eauto.
    unfold instr_is_nop in *. 
    rewrite Hipc in *.
    destruct ipc ; try congruence.
    simpl in *. destruct Hinsuccpc; subst; intuition.
Qed.


(** * Utility lemmas and useful tactics *)

Lemma fold_left_update_ctx_propagate_error : 
  forall size preds def def_phi clean_code live  ppoints e,
  fold_left (update_ctx size preds def def_phi clean_code live) ppoints
  (Error e) = Error e.
Proof.
  induction ppoints; auto.
Qed.

Ltac reduce_get_option := 
  match goal with
    [ id: context [get_option ?x _] |- _ ] => 
    generalize id; clear id; case_eq x; simpl; intros; 
      try (rewrite fold_left_update_ctx_propagate_error in *; try congruence)
  end.

Ltac reduce_is_joinpoint := 
  match goal with
    [ id: context [is_joinpoint ?preds ?n] |- _ ] => 
    generalize id; clear id; case_eq (is_joinpoint preds n); simpl; intros; 
      try (rewrite fold_left_update_ctx_propagate_error in *; try congruence)
  end.

Ltac reduce_forall3_ptree := 
  match goal with
    [ id: context [forall3_ptree ?f ?m1 ?m2 ?m3] |- _ ] => 
    generalize id; clear id; case_eq (forall3_ptree f m1 m2 m3); simpl; intros; 
      try (rewrite fold_left_update_ctx_propagate_error in *; try congruence)
  | [ |- context [forall3_ptree ?f ?m1 ?m2 ?m3] ] => 
    case_eq (forall3_ptree f m1 m2 m3); simpl; intros Hforall2; 
      try (rewrite fold_left_update_ctx_propagate_error in *; try congruence)
  end.

Ltac rewrite_some :=
 match goal with
  |  [ id: _ = Some _ |- _] => rewrite id
  |  [ id: _ = None |- _] => rewrite id
  end.

Lemma op_forall3_ptree : forall (def_phi:PTree.t index) (live: Regset.t) n (x:option index),
    (fun x i i' o =>
       
    let i := match i with None => dft_pos | Some i => i end in
      let i' := match i' with None => dft_pos | Some i => i end in
        match o with
          | Some _ => true
          | None =>

            peq i i' || negb (Regset.mem x live)
        end) n None None x = true.
Proof.
  simpl; auto.
  intros.
  destruct x; auto.
Qed.

Lemma upd_list_some : forall l (g:PTree.t index) G n, 
  (In n l /\ (upd_list l g G) ! n = Some g) \/
  (~ In n l /\ (upd_list l g G) ! n = G !n).
Proof.
  induction l; simpl; intros; auto.
  elim IHl with g (PTree.set a g G) n; intuition auto.
  rewrite PTree.gsspec in H1; destruct peq; intuition auto.
Qed.

(** * Properties of [build_phi_block] and [update_ctx] *)

Section fold_left_update_ctx_prop.

Variable code: RTL.code.
Variable preds: PTree.t (list node).
Variable def: PTree.t index.
Variable def_phi: PTree.t (PTree.t index).

Hypothesis pred_hyp2: forall n1 n2 n' ins1 ins2, 
  code!n1 = Some ins1 -> In n' (RTL.successors_instr ins1) -> 
  code!n2 = Some ins2 -> In n' (RTL.successors_instr ins2) -> 
  is_joinpoint preds n' = false -> n1=n2.

Hypothesis pred_hyp3 : forall i j ins,
  code ! i = Some ins ->
  In j (RTLdfs.successors_instr ins) ->
  is_joinpoint  preds j = true ->
  ins = RTL.Inop j.

Ltac kill_error :=
  rewrite fold_left_update_ctx_propagate_error in *; try congruence.

Ltac and_proof :=
  match goal with
    [ |- ?A /\ ?B ] => 
    let h := fresh "Pr" in
      (assert (h:A); [idtac|split; [exact h|and_proof]])
  | _ => idtac
  end.

Ltac new_code_tac :=
  match goal with
    |  h:forall ii, forall inss, (PTree.set ?x ?ins ?m) ! ii = Some inss -> _ |- _ =>
       let H := fresh "Hgss" in 
       (generalize (h _ _ (PTree.gss x ins m)); intros H)
  end.

Ltac clean := 
  try new_code_tac;
  repeat 
  match goal with
    | id1: ?a = ?b1, id2: ?a = ?b2 |- _ => rewrite id1 in id2; inv id2
end.

Ltac in_succ_case :=
  match goal with
  |  id: In ?j (successors_instr ?inst) |- _ =>
    simpl in id; 
    repeat destruct id as [id|id]; subst; 
    try (elim id; fail) ;
    try (match goal with
         | id1 : ?g1 ! ?n1 = Some _ |- ?g1 ! ?n1 <> None =>
           elim id1; fail
         end)
  |  id: In ?j (RTLdfs.successors_instr ?inst) |- _ => simpl in id; 
      repeat destruct id as [id|id]; subst; try (elim id; fail)
  end.

Hint Extern 4 (In _ (successors_instr _)) => simpl: core.
Hint Extern 4 (In _ (RTLdfs.successors_instr _)) => simpl: core.

Variant is_out_instr : instruction -> Prop:=
| Out_jumptable: forall arg, 
  is_out_instr (Ijumptable arg nil)
| Out_tailcall: forall sig fn args, 
  is_out_instr (Itailcall sig fn args)
| Out_return : forall or,
  is_out_instr (Ireturn or).

Lemma build_phi_block_correct: forall size preds live def_phi G phicode pc phicode'
  (EQ:build_phi_block size preds live def_phi G (OK phicode) pc = OK phicode'),
  (forall i phi, phicode'!i = Some phi -> (i=pc \/ phicode!i = Some phi)) /\
  (exists phi, phicode'!pc = Some phi) /\
  (forall i phi, phicode!i = Some phi -> phicode'!i = Some phi
    \/ (i=pc /\ phicode!pc <> None)).
Proof.
  unfold build_phi_block; simpl; intros size preds0 live def_phi0 G phicode pc phicode'.
  case_eq (preds0!pc); simpl; intros prd Hprd; [idtac|congruence].
  case_eq (def_phi0!pc); simpl; intros df Hdf; [idtac|congruence].
  destruct (@forall_ptree positive).
  intros EQ; inv EQ.
  repeat split.

  intros i phi; rewrite PTree.gsspec; destruct peq; auto.

  rewrite PTree.gss; eauto.

  intros HH i phi; rewrite PTree.gsspec; destruct peq; [subst|auto].
  right; split; congruence.
  congruence.
Qed.

Lemma fold_build_phi_block_some : forall f size live def_phi G jpoints phiblock acc,
  fold_left
  (build_phi_block size
    (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) live def_phi G)
  jpoints acc = OK phiblock ->
  exists a, acc = OK a.
Proof.
  induction jpoints; simpl; intros; eauto.
  exploit IHjpoints; eauto.
  intros [a' Ha].
  destruct acc; eauto.
  unfold build_phi_block in Ha.
  destruct (get_option (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr)!a); 
    simpl in Ha; try congruence.
  destruct (def_phi0!a); simpl in Ha; try congruence.
  destruct (@forall_ptree positive); congruence.
Qed.

Lemma fold_build_phi_block_def_phi_same : forall size f live def_phi G jpoints phiblock phiblock',
  fold_left
  (build_phi_block size
    (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) live def_phi G)
  jpoints (OK phiblock) = OK phiblock' ->
  forall pc, ~ In pc jpoints -> phiblock!pc = phiblock'!pc.
Proof.
  induction jpoints; simpl; intros.
  inv H; auto.
  exploit fold_build_phi_block_some; eauto; intros [b Hb].
  rewrite Hb in H.
  exploit IHjpoints; eauto; intros Heq; clear IHjpoints H.
  rewrite <- Heq; clear Heq.
  unfold build_phi_block in *.
  destruct ((make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr)!a); simpl in *; try congruence.
  destruct (def_phi0!a); simpl in *; try congruence.
  destruct (@forall_ptree positive).
  inv Hb.
  rewrite PTree.gso; auto.
  congruence.
Qed.

Lemma fold_build_phi_block_def_phi_some : forall size f live def_phi G jpoints phiblock acc,
  fold_left
  (build_phi_block size
    (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) live def_phi G)
  jpoints acc = OK phiblock ->
  forall pc, In pc jpoints -> exists d, 
    def_phi!pc = Some d /\ 
    forall x i, d!x = Some i -> i<>xH.
Proof.
  induction jpoints; simpl; intros.
  intuition.
  destruct H0; subst; eauto.
  exploit fold_build_phi_block_some; eauto; intros [a Ha].
  unfold build_phi_block in *.
  destruct ((make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr)!pc); simpl in *; try congruence.
  destruct (def_phi0!pc); simpl in *; eauto.
  exists t; split; auto.
  case_eq (forall_ptree (fun _ xdef : positive => negb (Pos.eqb 1 xdef)) t); intros Hb.
  red; intros; subst.
  exploit forall_ptree_true; eauto.
  (* simpl; congruence. *)
  rewrite Hb in *; congruence.
  congruence.
Qed.

Lemma fold_build_phi_block_value: forall size f live def_phi G jpoints phiblock acc,
  fold_left
  (build_phi_block size 
    (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) live def_phi G)
  jpoints acc = OK phiblock -> 
  forall pc pred d, In pc jpoints -> 
    (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr)!pc = Some pred ->
    def_phi!pc = Some d ->
    let live := live pc in 
      let get_Gpreds := 
        (fun pc_pred => 
          match G ! pc_pred with
            | None => (* should not happen *) PTree.empty _
            | Some m => m
          end) in
  let new_phi_block :=
    PTree.fold
      (fun phis x xdef =>
        if Regset.mem x live then
          let phi_args := List.map
            (fun pc0 => Bij.pamr size (x,read_gamma (get_Gpreds pc0) x)) pred in
            let phi_def := Bij.pamr size (x,xdef) in
              (Iphi phi_args phi_def)::phis
          else phis
        ) d nil in
      phiblock!pc = Some new_phi_block.
Proof.
  induction jpoints; simpl; intros.
  intuition.
  destruct H0; subst; eauto.
  exploit fold_build_phi_block_some; eauto; intros [a Ha].
  destruct (classic (In pc jpoints)); eauto.
  rewrite Ha in H.
  exploit fold_build_phi_block_def_phi_same; eauto; intros Heq.
  rewrite <- Heq; clear IHjpoints; clear Heq.
  unfold build_phi_block in *.
  rewrite H1 in *; simpl in *.
  rewrite H2 in *; simpl in *.
  destruct (@forall_ptree); try congruence.
  destruct acc ; inv Ha.
  rewrite PTree.gss; auto.
Qed.

Lemma in_params_of_builtin_args_erase : forall size g,
    (forall x, Bij.valid_index size (read_gamma g x) = true) ->  
    forall l ri r i,
    In ri 
       (params_of_builtin_args (map (map_builtin_arg (λ x, Bij.pamr size (x, read_gamma g x))) l)) ->
    Bij.rmap size ri = (r, i) ->
    read_gamma g r = i.
Proof.
  induction l ; simpl; intros.
  - intuition.
  - apply in_app_or in H0. inv H0.  
    + clear IHl.
      induction a ; simpl in * ; intros; try intuition auto; try inv H; auto.
      * rewrite <- H0 in H1.
        rewrite Bij.BIJ1 in H1; auto. inv H1. auto.
      * apply in_app_or in H2.
        inv H2; eauto.
      * apply in_app_or in H2.
        inv H2; eauto.
    + eapply IHl ; eauto.
Qed.

Lemma in_params_of_builtin_args_valid : forall size g,
    (forall x, Bij.valid_index size (read_gamma g x) = true) ->  
    forall l ri,
    In ri 
       (params_of_builtin_args (map (map_builtin_arg (λ x, Bij.pamr size (x, read_gamma g x))) l)) ->
    Bij.valid_reg_ssa size ri = true. 
Proof.
  induction l ; simpl; intros.
  - intuition.
  - apply in_app_or in H0. inv H0.  
    + clear IHl.
      induction a ; simpl in * ; intros; try intuition auto; try inv H; auto.
      * subst. eapply Bij.from_valid_index_to_valid_reg_ssa; eauto. 
      * apply in_app_or in H1.
        inv H1; eauto.
      * apply in_app_or in H1.
        inv H1; eauto.
    + eapply IHl ; eauto.
Qed.

Lemma fold_build_phi_block_correct : forall size f live def_phi G jpoints m phicode,
  fold_left
  (build_phi_block size
    (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) live def_phi G)
  jpoints (OK m) = OK phicode ->
  (forall i phi, phicode!i = Some phi -> (In i jpoints) \/ m!i = Some phi) /\
  (forall i, In i jpoints -> exists phi, phicode!i = Some phi) /\
  (forall i phi, m!i = Some phi -> exists phi, phicode!i = Some phi).
Proof.
  intros f live0 def_phi0 G.
  induction jpoints; simpl; intros.
  inv H; intuition auto.
  eauto.
  exploit fold_build_phi_block_some; eauto; intros [b Hb].
  rewrite Hb in *.
  exploit IHjpoints; eauto; intros [T1 [T2 T3]].
  exploit build_phi_block_correct; eauto; intros [B1 [B2 B3]].
  split.
  intros i phi Hp.
  elim T1 with i phi; auto.
  intros.
  elim B1 with i phi; auto.
  split.
  intros i Hi; intuition; subst; eauto.
  destruct B2; eauto.
  intros i phi HH; intuition.
  exploit B3; eauto.
  destruct 1; eauto.
  destruct H0; subst.
  destruct B2; eauto.
Qed.

Lemma map_map_erase : forall size f l,
    (forall x, Bij.valid_index size (f x) = true) ->
    map (erase_reg size) (map (λ x : reg, Bij.pamr size (x, f x)) l) = l.
Proof.
  induction l ; intros; simpl ; eauto.
  rewrite IHl; auto.
  unfold erase_reg.
  rewrite Bij.BIJ1; auto.
Qed.

Lemma erase_reg_pamr : forall size r df,
    (Bij.valid_index size df = true) -> 
    (erase_reg size (Bij.pamr size (r, df))) = r.
Proof.
  intros.
  unfold erase_reg.
  rewrite Bij.BIJ1; auto.
Qed.

Lemma map_builtin_res_id : forall size i,
    Bij.valid_index size i = true -> 
    forall br,
    map_builtin_res (erase_reg size) (map_builtin_res (fun r => Bij.pamr size (r, i)) br) = br.
Proof.
  induction br ; intros; eauto.
  - simpl. unfold erase_reg.
    rewrite Bij.BIJ1; auto.
  - simpl. congruence.
Qed.

Lemma map_builtin_arg_id : forall size f,
    (forall x, Bij.valid_index size (f x) = true) ->
    forall a,
      map_builtin_arg (erase_reg size) (map_builtin_arg (λ x1 : reg, Bij.pamr size (x1, f x1)) a) = a.
Proof.
  induction a; intros; eauto.
  - simpl.
    unfold erase_reg.
    rewrite Bij.BIJ1; auto.
  - simpl; congruence.
  - simpl; congruence.
Qed.
Lemma map_map_builtin_arg_id : forall size f,
    (forall x, Bij.valid_index size (f x) = true) ->
    forall l,
      (map  (λ x0,
             map_builtin_arg (erase_reg size)
                             (map_builtin_arg (λ x1, Bij.pamr size (x1, f x1)) x0)) l) = l.
Proof.
  induction l; intros; eauto.
  simpl.
  rewrite IHl; eauto.
  rewrite map_builtin_arg_id; auto.
Qed.

Variable size: nat.

Hypothesis dft_pos_valid: Bij.valid_index size dft_pos = true.
Hypothesis def_hyp: forall x i, def ! x = Some i -> Bij.valid_index size i = true.
Hypothesis def_phi_hyp: forall pc dphi,
    def_phi ! pc = Some dphi ->
    forall x i, dphi ! x = Some i -> Bij.valid_index size i = true.

Definition valid_ttgamma (G: ttgamma): Prop :=
  forall pc g, G ! pc = Some g ->
               forall x i, read_gamma g x = i -> Bij.valid_index size i = true.

Lemma upd_list_valid_ttgamma : forall l G g, 
    (forall x, Bij.valid_index size (read_gamma g x) = true)  -> 
    valid_ttgamma G ->
    valid_ttgamma (upd_list l g G).
Proof.
  clear.
  induction l; intros; auto.
  simpl.
  eapply IHl; eauto.
  intros pc; intros.
  destruct (peq pc a).
  - subst. rewrite PTree.gss in H1; auto.
    inv H1. auto.
  - rewrite PTree.gso in H1; eauto.
Qed.

Lemma case_in_map_fst : forall A B,
    (forall x1 x2: A, { x1 = x2 } + { x1 <> x2} ) ->
    forall (x:A) l,
    ~ In x (map fst l) \/ exists i:B, In (x,i) l.
Proof.
  induction l ; intros.
  - left; eauto.
  - inv IHl.
    + destruct (X (fst a) x).
      * subst. right.
        exists (snd a).
        rewrite <- surjective_pairing; auto.
      * left. intro. inv H0; auto.
    + destruct H as [i Hi].
      right; eauto.
Qed.      

Lemma fold_left_update_ctx_prop: forall live
  ppoints G new_code juncpoints G' new_code' juncpoints',
  fold_left (update_ctx size preds def def_phi code live) ppoints 
  (OK (G,new_code,juncpoints)) = OK (G',new_code',juncpoints') ->
  list_norepet ppoints ->
  (forall n1 n2 ins g, 
    G ! n2 = Some g -> 
    In n1 ppoints -> 
    code ! n1 = Some ins ->
    In n2 (RTLdfs.successors_instr ins) ->
    is_joinpoint preds n2 = true) ->
  (forall j gj dphi,
    G!j = Some gj -> 
    is_joinpoint preds j = true ->
    def_phi!j = Some dphi ->
    forall x i, Regset.mem x (live j)=true -> dphi!x = Some i -> read_gamma gj x = i) ->
  (forall i, In i ppoints -> new_code!i = None) ->
  (forall i g, is_joinpoint preds i = true -> G!i = Some g -> In i juncpoints) ->
  (valid_ttgamma G) ->

  (* ******************************** *)

  (forall n g, G ! n = Some g -> G' ! n = Some g) /\
  (forall i ins, new_code!i = Some ins -> new_code'!i = Some ins) /\
  (forall i, In i ppoints -> 
    get_opt successors_instr (new_code'!i) = get_opt RTLdfs.successors_instr (code!i)) /\
  (forall i, In i ppoints -> 
    get_opt (erase_instr size) (new_code'!i) = get_opt (fun x => x) (code!i)) /\
  (forall i j ins gi gj,
    In i ppoints ->
    new_code'!i = Some ins -> In j (successors_instr ins) ->
    G'!i = Some gi -> G'!j = Some gj -> 
    is_joinpoint preds j = false ->
    wt_instr size (read_gamma gi) ins (read_gamma gj)) /\
  (forall i ins gi,
    In i ppoints ->
    new_code'!i = Some ins -> is_out_instr ins ->
    G'!i = Some gi ->
    wt_instr size (read_gamma gi) ins (read_gamma gi)) /\
  (forall i j ins gi gj dphi,
    In i ppoints ->
    new_code'!i = Some ins -> In j (successors_instr ins) ->
    G'!i = Some gi -> G'!j = Some gj -> 
    is_joinpoint preds j = true ->
    def_phi!j = Some dphi ->
    (forall x i, dphi!x = Some i -> Regset.mem x (live j)=true -> read_gamma gj x = i) /\
    (forall x, dphi!x = None -> Regset.mem x (live j)=true -> read_gamma gi x = read_gamma gj x)) /\
  (forall i, In i juncpoints' -> In i juncpoints \/ is_joinpoint preds i = true) /\
  (forall i, In i juncpoints -> In i juncpoints') /\
  (forall i j ins, In i ppoints -> 
    code ! i = Some ins ->
    In j (RTLdfs.successors_instr ins) ->
    is_joinpoint preds j = true -> In j juncpoints') /\
  (forall i ins, new_code'!i = Some ins -> In i ppoints \/ new_code!i = Some ins) /\
  (forall i ins, new_code'!i = Some ins ->
                 new_code!i = Some ins \/ G'!i <> None /\ 
                                          wt_eidx size (fun _ => xH) ins /\
                                          forall j, In j (successors_instr ins) -> G'!j <> None)  /\
  (forall i g, is_joinpoint preds i = true -> G'!i = Some g -> In i juncpoints') /\
  (valid_ttgamma G').
Proof.
  induction ppoints; simpl.
  - intros G new_code juncpoints G' new_code' juncpoints' H H0 H1 HVALID.
    repeat split; try (intuition auto; fail).
    inv H; auto.
    inv H; auto.
    inv H; auto.
    inv H; auto.
    inv H; intuition auto.
    inv H; intuition auto.
    inv H; intuition auto.
    inv H; intuition auto.
  - intros G new_code juncpoints G' new_code' juncpoints'.
    case_eq (code ! a); [intros ins Hins|intro; simpl; kill_error].
    case_eq (G ! a); [intros g Hg|intro; simpl; kill_error].
    destruct ins; simpl in *.

    + case_eq (is_joinpoint  preds n); intros Hj; try kill_error.

      * { case_eq (def_phi ! n); [intros dphi Hdphi|simpl; intros; kill_error].
          simpl.
          case_eq (G ! n); simpl; [intros g' Hg'|intros Hg'].
          - reduce_forall3_ptree.
            (* Inop + is_joinpoint + G!n = Some _ *)
            
            intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
            inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
            elim IHppoints with (1:=Heq) (2:=Hln2);
              [intros HINV [HINV1 [HINV4 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV11 [HINV12 HINVVALID]]]]]]]]]]]]
              |eauto|eauto|idtac|eauto|eauto].
            + and_proof; auto.

              * intros i ins Hn; eapply HINV1.
                rewrite PTree.gsspec; destruct peq; subst; auto.
                rewrite INV3 in Hn; auto; congruence.
              * intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].   
                rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
              * intros i Hin; destruct Hin; [subst|apply HINV2; auto; fail].   
                rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
              * intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun ; destruct Hin; [subst| try eapply HINV6;eauto;fail].
                repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
                clean; in_succ_case; clean.
              * intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV3 with i;auto;fail].
                clean; inv Hout.
              * intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV6;eauto;fail].
                assert (G2:G!i=Some g /\ G!n = Some g') by (split; auto).
                repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
                clean ; in_succ_case; clean. 
                generalize (@gforall3_ptree _ _ _ (@op_forall3_ptree dpi (live j)) _ _ _ Hforall2);
                  clear Hforall2; intros Hforall2.
                assert (Hforall2':forall x, dpi! x = None -> Regset.mem x (live j) = true -> read_gamma g x = read_gamma g' x).
                { intros x H HT.
                  unfold read_gamma, index.
                  generalize (Hforall2 x).
                  rewrite HT; simpl; rewrite orb_false_r.
                  rewrite H.
                  destruct (@PTree.get positive x g); destruct (@PTree.get positive x g');
                    destruct peq; intros H0; intuition.
                }    
                clear Hforall2.
                { split; intros.
                  - destruct G2; exploit (INV2 j); eauto.
                  - simpl; auto.
                }
              * intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV9; eauto; fail].
                clean; in_succ_case; clean.
                apply HINV8; eauto.
              * intros i ins Hs; elim HINV10 with (1:=Hs); auto.
                rewrite PTree.gsspec; destruct peq; subst; auto.
              * intros i ins Hs; elim HINV11 with (1:=Hs); auto.
                rewrite PTree.gsspec; destruct peq; subst; auto.
                repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
                intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
                clean ; in_succ_case; clean. congruence.

            + intros i Hin; rewrite PTree.gsspec; destruct peq; subst; intuition.

          - (* Inop + is_joinpoint + G!n = None *)
            intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
            inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
            elim IHppoints with (1:=Heq) (2:=Hln2);
              [intros HINV [HINV1 [HINV4 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV11 [HINV12 HINVVALID]]]]]]]]]]]]
              |idtac|idtac|idtac|idtac|idtac].
            + and_proof; auto.
              * intros; eapply HINV; eauto.
                rewrite PTree.gsspec; destruct peq; auto.
                congruence.
              * intros i ins Hn; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
                rewrite INV3 in Hn; auto; congruence.  
              * intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
                rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
              * intros i Hin; destruct Hin; [subst|apply HINV2; auto; fail].
                rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
              * intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV5;eauto;fail].
                repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
                clean; in_succ_case; clean.
              * intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV3 with i;auto;fail].
                clean; inv Hout.
              * intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV6;eauto;fail].
                repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
                clean; in_succ_case; clean.
                generalize (HINV j); rewrite PTree.gss; clear HINV.
                intros HINV; generalize (HINV _ (refl_equal _)); clear HINV; intros HINV.
                clean.
                assert (forall A l g x,
                           ~ In x (List.map (@fst _ A) l) ->
                           (fold_left (fun a p =>
                                         if Regset.mem (fst p) (live j)
                                         then PTree.set (fst p) (snd p) a
                                         else a) l g) ! x = g ! x).
                { induction l; simpl; intros.
                  - auto.    
                  - rewrite IHl; auto.
                    destruct Regset.mem; auto.
                    rewrite PTree.gso; auto.
                }
                assert (forall x (i:index) l g,
                           In (x,i) l ->
                           Regset.mem x (live j) = true ->
                           list_norepet (List.map (@fst _ _) l) ->
                           (fold_left (fun a p =>
                                         if Regset.mem (fst p) (live j)
                                         then PTree.set (fst p) (snd p) a
                                         else a) l g) ! x = Some i).
                { induction l; simpl; intros.
                  - intuition.
                  - inv H2.
                    destruct H0; subst; simpl in *.    
                    + rewrite H; try rewrite H1.
                      * rewrite PTree.gss; auto.
                      * auto.
                    + auto.
                }
                split; intros.
                rewrite PTree.fold_spec.
                unfold read_gamma; rewrite (H0 x i0); auto.
                apply PTree.elements_correct; auto.
                apply PTree.elements_keys_norepet; auto.
                rewrite PTree.fold_spec.  
                unfold read_gamma; rewrite H; auto.
                red; intros.
                elim list_in_map_inv with (1:= H3).
                intros (x',i'); simpl; destruct 1; subst.
                rewrite (PTree.elements_complete dpi x' i') in H1; congruence.

              * intros i Hin; elim HINV7 with i; simpl; intuition.
                (* subst; auto. *)
              * intros i j ins Hin Hcode1 Hcode2 Hjun; destruct Hin; [subst|eapply HINV9; eauto; fail]. 
                clean; in_succ_case; clean.
                apply HINV8; auto.
              * intros i ins Hs; elim HINV10 with (1:=Hs); auto.
                rewrite PTree.gsspec; destruct peq; subst; auto. 
              * intros i ins Hs; elim HINV11 with (1:=Hs); auto.
                rewrite PTree.gsspec; destruct peq; subst; auto.
                repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
                intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
                clean ; in_succ_case; clean. congruence.

            + intros; rewrite PTree.gsspec in H; destruct peq; subst; auto.
              eauto.
            + (* PO2 *)
              intros j gj dphi0 H H0 H1 x i HR H2.
              rewrite PTree.gsspec in H; destruct peq; [subst|eapply INV2; eauto; fail].
              assert (forall A l g x,
                         ~ In x (List.map (@fst _ A) l) ->
                         (fold_left (fun a p =>
                                       if Regset.mem (fst p) (live n)
                                       then PTree.set (fst p) (snd p) a
                                       else a) l g) ! x = g ! x).
              { induction l; simpl; intros.
                - auto.
                - rewrite IHl; auto.
                  clear HR; destruct Regset.mem; auto.
                  rewrite PTree.gso; auto.
              }
              assert (forall x (i:index) l g,
                         In (x,i) l ->
                         Regset.mem x (live n) = true ->
                         list_norepet (List.map (@fst _ _) l) ->
                         (fold_left (fun a p =>
                                       if Regset.mem (fst p) (live n)
                                       then PTree.set (fst p) (snd p) a
                                       else a) l g) ! x = Some i).
              { induction l; simpl; intros.
                - intuition.
                - inv H6.
                  destruct H4; subst; simpl in *.
                  rewrite H3.
                  rewrite H5.
                  rewrite PTree.gss; auto.
                  apply H9.
                  auto.
              }
              inv H.
              rewrite PTree.fold_spec.
              unfold read_gamma; rewrite (H4 x i); auto.
              apply PTree.elements_correct; auto.
              clean; auto.
              apply PTree.elements_keys_norepet; auto.
            + (* PO3 *)
              intros; rewrite PTree.gsspec; destruct peq; subst; intuition.
            + (* PO4 *)
              intros.
              rewrite PTree.gsspec in H0; destruct peq; subst; simpl; eauto.

            + (* PO5 *)
              intros pc; intros.
              rewrite PTree.gsspec in H; destruct peq; [subst | eapply INVVALID; eauto].
              assert (forall l g x,
                         ~ In x (List.map (@fst _ _) l) ->
                         read_gamma (fold_left (fun a p =>
                                       if Regset.mem (fst p) (live n)
                                       then PTree.set (fst p) (snd p) a
                                       else a) l g) x =  read_gamma g x).
              { induction l; simpl; intros.
                - auto.
                - rewrite IHl; auto.
                  destruct Regset.mem; auto.
                  unfold read_gamma.
                  rewrite PTree.gso; auto.
              }

              assert (forall l x (i:index) g,
                         In (x,i) l ->
                         list_norepet (List.map (@fst _ _) l) ->
                         (forall y i, In (y, i) l -> Bij.valid_index size i = true) ->
                         (forall x, Bij.valid_index size (read_gamma g x) = true) ->
                         (forall x, Bij.valid_index size (read_gamma (fold_left (fun a p =>
                                       if Regset.mem (fst p) (live n)
                                       then PTree.set (fst p) (snd p) a
                                       else a) l g) x) = true)).
              { induction l; simpl; intros.
                - intuition.
                - inv H2.
                  destruct H1; subst; simpl in *. 
                  -- assert (HCASES: ~ In x1 (map fst l) \/ exists i, In (x1,i) l)
                      by (eapply case_in_map_fst with (1:= peq); eauto).
                     destruct HCASES as [CASE | [i1 CASE]].
                     ++ rewrite H0; auto.
                        destruct Regset.mem.
                        ** destruct (peq x0 x1).
                           --- subst. unfold read_gamma.
                               rewrite PTree.gss; auto.
                               eauto. 
                           --- unfold read_gamma.
                               rewrite PTree.gso; auto.
                               apply H4.
                        ** eauto.
                     ++ rewrite (IHl x1 i1); auto.
                        ** eauto.
                        ** intros.
                           destruct Regset.mem.
                           --- destruct (peq x0 x2).
                               +++ subst. unfold read_gamma.
                               rewrite PTree.gss; auto.
                               eauto.
                               +++ unfold read_gamma.
                               rewrite PTree.gso; auto.
                               case_eq (g1 ! x2); intros; auto.
                               unfold read_gamma in H4.
                               specialize (H4 x2); auto.
                               rewrite H1 in H4.  auto.
                           --- auto.
                  -- apply (IHl x0 i); auto.
                     ++ eauto.
                     ++ intros. destruct Regset.mem.
                        ** destruct (peq (fst a0) x2).
                           --- subst. unfold read_gamma.
                               rewrite PTree.gss; auto.
                               apply (H3 (fst a0) (snd a0)); auto.
                               rewrite <- surjective_pairing; auto.
                           --- unfold read_gamma.
                               rewrite PTree.gso; auto.
                               apply H4; auto.
                        ** eauto.
              }
              inv H.
              rewrite PTree.fold_spec.
              assert (HCASES: ~ In x (map fst (PTree.elements dphi)) \/ exists i, In (x,i) (PTree.elements dphi))
                by (eapply case_in_map_fst with (1:= peq); eauto).
              destruct HCASES as [HCASE|[i HCASE]].
              * rewrite H0; eauto.
              * rewrite (H1 _ x i); auto using PTree.elements_keys_norepet.
                intros. 
                eapply def_phi_hyp with (x:= y); eauto.
                apply PTree.elements_complete; auto.
                eauto.
        }
      * { (* Inop + not is_joinpoint *)
        intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
        inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
        elim IHppoints with (1:=Heq) (2:=Hln2);
          [intros HINV [HINV1 [HINV4 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV11 [HINV12 HINVVALID]]]]]]]]]]]]
          |idtac|idtac|idtac|idtac|idtac].
        - and_proof; auto.
          + intros; eapply HINV; eauto.
            rewrite PTree.gsspec; destruct peq; auto.
            subst.
            exploit INV1; eauto.
            congruence.
          + intros i ins Hn; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
            rewrite INV3 in Hn; auto; congruence.
          + intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
          + intros i Hin; destruct Hin; [subst|apply HINV2; auto; fail].  
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
          + intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV5;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean; in_succ_case; clean.
            rewrite (HINV j g) in Hgj.
            inv Hgj; constructor.
            rewrite PTree.gss; auto.
          + intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV3 with i;auto;fail].
            clean; inv Hout.
          + intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV6;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean; in_succ_case; clean.
          + intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV9; eauto; fail].
            clean; in_succ_case; clean. 
          + intros i ins Hs; elim HINV10 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto. 
          + intros i ins Hs; elim HINV11 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
            in_succ_case.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
        - (* PO1 *)
          intros n1 n2 ins g' T1 T2 T3 T4.
          rewrite PTree.gsspec in T1; destruct peq; subst; auto.
          assert (n1=a) by (eapply pred_hyp2; eauto; simpl; auto).
          subst; clean.
          intuition.
          eauto.
        - (* PO2 *)
          intros j gj dphi H H0 H1 x i H2.
          rewrite PTree.gsspec in H; destruct peq; [subst; congruence|eauto].
        - (* PO3 *)
          intros; rewrite PTree.gsspec; destruct peq; subst; intuition.
        - (* PO4 *)
          intros.
          rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence; eauto.
        - (* PO5 *)
          unfold valid_ttgamma. intros.
          destruct (peq n pc).
          + subst. rewrite PTree.gss in H. inv H.
            eapply INVVALID; eauto.
          + rewrite PTree.gso in H; auto.
            eapply INVVALID; eauto.
        }
        
    + { (* Iop *)
        case_eq (def ! a); simpl; [intros df Hdef|intro; kill_error].
        case_eq (negb (Pos.eqb 1 df)); [intros Hnp|simpl; kill_error].
        intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
        inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.  
        elim IHppoints with (1:=Heq) (2:=Hln2);
          [intros HINV [HINV1 [HINV4 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV11 [HINV12 HINVVALID]]]]]]]]]]]]
          |idtac|idtac|idtac|idtac|idtac]; clear Heq.
        - and_proof; auto.
          + intros; eapply HINV; eauto.
            rewrite PTree.gsspec; destruct peq; auto.
            subst.
            exploit INV1; eauto.
            intros.
            exploit pred_hyp3; eauto.
            congruence. 
          + intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
            rewrite INV3 in H; auto; congruence.
          + intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
          + intros i Hin; destruct Hin; [subst|apply HINV2; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
            unfold erase_instr, get_opt ; simpl.
            rewrite map_map_erase with (f:= (read_gamma g)) ; eauto.
            rewrite erase_reg_pamr; eauto.
          + intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV5;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            replace (read_gamma gj) with (update (read_gamma gi) r df).

            * clean; in_succ_case; clean.
              constructor.
              -- intros.
                 elim list_in_map_inv with (1:= H); intros xx [V1 V2]; subst.
                 assert (Bij.valid_index size (read_gamma g xx) = true) by eauto.
                 rewrite Bij.BIJ1 in H0; auto. inv H0; auto. 
              -- rewrite Bij.BIJ1; eauto.
              -- intros.
                 inv H.
                 ++ eapply HINVVALID with (x:= r) (i:= i0); eauto.
                    unfold read_gamma. rewrite PTree.gss; auto.
                    rewrite Bij.BIJ1 in H0; eauto. inv H0. auto.
                 ++ apply list_in_map_inv in H1; auto.
                    destruct H1 as [rx [EQ Hin]]. subst.                  
                    rewrite Bij.BIJ1 in H0; auto. inv H0.
                    eapply HINVVALID with (pc:= i) (x:= r0); eauto.
                    eauto.
              -- intros.
                 inv H.
                 ++ eapply Bij.from_valid_index_to_valid_reg_ssa; eauto.
                 ++ apply list_in_map_inv in H0; auto.
                    destruct H0 as [rx [EQ Hin]]. subst.                  
                    eapply Bij.from_valid_index_to_valid_reg_ssa; eauto. 
              
            * clean.
              in_succ_case ; clean.
              generalize (HINV _ _ (PTree.gss _ _ _)); intros.
              apply extensionality; unfold update; intros; destruct peq; unfold read_gamma.
              subst.
              rewrite PTree.gss; auto.
              rewrite PTree.gso; auto.
          + intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV3 with i;auto;fail].
            clean; inv Hout.
          + intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV6;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean; in_succ_case; clean.
            exploit pred_hyp3; eauto; intro T; inv T.
          + intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV9; eauto; fail].
            clean; in_succ_case; clean.
            exploit pred_hyp3; eauto; intro T; inv T.
          + intros i ins Hs; elim HINV10 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto. 
          + intros i ins Hs; elim HINV11 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            intros Hss; inv Hss; right; repeat split; try congruence; intros.
            assert (Bij.valid_index size df = true) by eauto.
            econstructor; eauto.
            eapply Bij.BIJ1; eauto.
            intros EE; rewrite <- (Pos.eqb_eq xH df) in EE; destruct (Pos.eqb xH df); simpl in *; congruence.
            in_succ_case.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
        - (* PO1 *)
          intros n1 n2 ins g' T1 T2 T3 T4.
          rewrite PTree.gsspec in T1; destruct peq; subst; auto.
          case_eq (is_joinpoint preds n); intros; auto.
          assert (n1=a).
          eapply pred_hyp2; eauto; simpl; auto.
          subst; intuition.
          eauto.
        - (* PO2 *)
          intros j gj dphi H H0 H1 x i H2.
          rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
          exploit pred_hyp3; eauto.
          congruence.
        - (* PO3 *)
          intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
        - (* PO4 *)
          intros.
          rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence; eauto.
          exploit pred_hyp3; eauto; intro T; inv T.
        - (* PO5 *)
          unfold valid_ttgamma. intros.
          destruct (peq pc n).
          + subst. rewrite PTree.gss in H. inv H.
            destruct (peq r x).
            * subst. unfold read_gamma. rewrite PTree.gss.
              eauto.
            * unfold read_gamma. rewrite PTree.gso; auto.
              case_eq (g ! x); auto; intros.
              eapply INVVALID with (pc:= a) (x:= x); eauto.
              unfold read_gamma. rewrite H; auto.
          + rewrite PTree.gso in H; auto. eapply INVVALID; eauto.
      }

    + { (* Iload *)
        case_eq (def ! a); simpl; [intros df Hdef|intro; kill_error].
        case_eq (negb (Pos.eqb 1 df)); [intros Hnp|simpl; kill_error].
        intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
        inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
        elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV11 [HINV12 HINVVALID]]]]]]]]]]]]|idtac|idtac|idtac|idtac|idtac]; clear Heq.
        - and_proof; auto.
          + intros; eapply HINV; eauto.
            rewrite PTree.gsspec; destruct peq; auto.
            subst.
            exploit INV1; eauto.
            intros.
            exploit pred_hyp3; eauto.
            congruence.
          + intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
            rewrite INV3 in H; auto; congruence.
          + intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
          + intros i Hin; destruct Hin; [subst|apply HINV2; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
            unfold erase_instr, get_opt ; simpl.
            rewrite map_map_erase with (f:= (read_gamma g)) ; eauto.
            rewrite erase_reg_pamr; eauto.
            
          + intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV5;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            replace (read_gamma gj) with (update (read_gamma g) r df).
            clean; in_succ_case; clean.
            constructor.
            * intros.
              elim list_in_map_inv with (1:= H); intros xx [V1 V2]; subst.
              assert (Bij.valid_index size (read_gamma g xx) = true) by eauto.
              rewrite Bij.BIJ1 in H0; eauto. inv H0; auto. 
            * rewrite Bij.BIJ1 ; eauto.
            * intros. inv H.
              -- eapply HINVVALID; eauto.
                 unfold read_gamma. rewrite PTree.gss; auto.
                 rewrite Bij.BIJ1 in H0; eauto. inv H0. auto.
              -- apply list_in_map_inv in H1; auto.
                 destruct H1 as [rx [EQ Hin]]. subst.
                 rewrite Bij.BIJ1 in H0; auto. inv H0.
                 eapply HINVVALID with (pc:= i); eauto.
                 eauto.
            * intros. inv H.
              -- eapply Bij.from_valid_index_to_valid_reg_ssa; eauto. 
              -- apply list_in_map_inv in H0; auto.
                 destruct H0 as [rx [EQ Hin]]. subst.
                 eapply Bij.from_valid_index_to_valid_reg_ssa; eauto. 
            * generalize (HINV _ _ (PTree.gss _ _ _)); intros; clean.
              clean; in_succ_case; clean.
              apply extensionality; unfold update; intros; destruct peq; unfold read_gamma.
              subst. 
              rewrite PTree.gss; auto.
              rewrite PTree.gso; auto.
          + intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV3 with i;auto;fail].
            clean; inv Hout.
          + intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV6;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean; in_succ_case; clean.
            exploit pred_hyp3; eauto; intro T; inv T.
          + intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV9; eauto; fail].
            clean; in_succ_case; clean.
            exploit pred_hyp3; eauto; intro T; inv T.
          + intros i ins Hs; elim HINV10 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto. 
          + intros i ins Hs; elim HINV11 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            intros Hss; inv Hss; right; repeat split; try congruence; intros.
            assert (Bij.valid_index size df = true) by eauto.
            econstructor; eauto.
            eapply Bij.BIJ1; eauto.
            intros EE; rewrite <- (Pos.eqb_eq xH df) in EE; destruct (Pos.eqb xH df); simpl in *; congruence.
            in_succ_case.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
        - (* PO1 *)
          intros n1 n2 ins g' T1 T2 T3 T4.
          rewrite PTree.gsspec in T1; destruct peq; subst; auto.
          case_eq (is_joinpoint preds n); intros; auto.
          assert (n1=a).
          eapply pred_hyp2; eauto; simpl; auto.
          subst; intuition.
          eauto.
        - (* PO2 *)
          intros j gj dphi H H0 H1 x i H2.
          rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
          exploit pred_hyp3; eauto.
          congruence.
        - (* PO3 *)
          intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
        - (* PO4 *)
          intros.
          rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence; eauto.
          exploit pred_hyp3; eauto; intro T; inv T.
        - (* PO5 *)
          unfold valid_ttgamma. intros.
          destruct (peq pc n).
          + subst. rewrite PTree.gss in H. inv H.
            destruct (peq r x).
            * subst. unfold read_gamma. rewrite PTree.gss.
              eauto.
            * unfold read_gamma. rewrite PTree.gso; auto.
              case_eq (g ! x); auto; intros.
              eapply INVVALID with (pc:= a) (x:= x); eauto.
              unfold read_gamma. rewrite H; auto.
          + rewrite PTree.gso in H; auto. eapply INVVALID; eauto.
      } 
    + { (* Istore *)
        intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
        inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
        elim IHppoints with (1:=Heq) (2:=Hln2);
          [intros HINV [HINV1 [HINV4 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV11 [HINV12 HINVVALID]]]]]]]]]]]]
          |idtac|idtac|idtac|idtac|idtac]; clear Heq.
        + and_proof; auto.
          * intros; eapply HINV; eauto.
            rewrite PTree.gsspec; destruct peq; auto.
            subst.
            exploit INV1; eauto.
            intros.
            exploit pred_hyp3; eauto.
            congruence.
          * intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
            rewrite INV3 in H; auto; congruence.
          * intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
          * intros i Hin; destruct Hin; [subst|apply HINV2; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
            unfold erase_instr, get_opt ; simpl.
            rewrite map_map_erase with (f:= (read_gamma g)) ; eauto.
            rewrite erase_reg_pamr; eauto.
          * intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV5;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean; in_succ_case; clean.
            generalize (HINV _ _ (PTree.gss _ _ _)); intros; clean.

            econstructor 8 ; eauto. 
            -- intros. inv H. rewrite Bij.BIJ1 in H0; eauto. inv H0. auto.
               elim list_in_map_inv with (1:= H1); intros xx [V1 V2]; subst.
               rewrite Bij.BIJ1 in H0; eauto. inv H0. auto.
            -- intros. inv H.
               ++ eapply HINVVALID ; eauto.
                  rewrite Bij.BIJ1 in H0; eauto.
                  inv H0. eauto. 
               ++ apply list_in_map_inv in H1; auto.
                  destruct H1 as [rx [EQ Hin]]. subst.
                  eapply HINVVALID with (pc:= i); eauto.
                  rewrite Bij.BIJ1 in H0; eauto.
                  inv H0. eauto.
            -- intros. inv H.
               ++ eapply Bij.from_valid_index_to_valid_reg_ssa; eauto.
               ++ apply list_in_map_inv in H0; auto.
                  destruct H0 as [rx [EQ Hin]]. subst.
                  eapply Bij.from_valid_index_to_valid_reg_ssa; eauto.
                  
          * intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV3 with i;auto;fail].
            clean; inv Hout.
          * intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV6;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean; in_succ_case; clean.
            exploit pred_hyp3; eauto; intro T; inv T.
          * intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV9; eauto; fail].
            clean; in_succ_case; clean.
            exploit pred_hyp3; eauto; intro T; inv T.
          * intros i ins Hs; elim HINV10 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto. 
          * intros i ins Hs; elim HINV11 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
            in_succ_case.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
        + (* PO1 *)
          intros n1 n2 ins g' T1 T2 T3 T4.
          rewrite PTree.gsspec in T1; destruct peq; subst; auto.
          case_eq (is_joinpoint preds n); intros; auto.
          assert (n1=a).
          eapply pred_hyp2; eauto; simpl; auto.
          subst; intuition.
          eauto.
          (* PO2 *)
        + intros j gj dphi H H0 H1 x i H2.
          rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
          exploit pred_hyp3; eauto.
          congruence.
        + (* PO3 *)
          intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
        + (* PO4 *)
          intros.
          rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence; eauto.
          exploit pred_hyp3; eauto; intro T; inv T.
        + (* PO5 *)
          unfold valid_ttgamma. intros.
          destruct (peq pc n).
          * subst. rewrite PTree.gss in H. inv H.
            eauto.
          * rewrite PTree.gso in H; auto. eapply INVVALID; eauto.
      }
    + { (* Icall *)
        case_eq (def ! a); simpl; [intros df Hdef|intro; kill_error].
        case_eq (negb (Pos.eqb 1 df)); [intros Hnp|simpl; kill_error].
        intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
        inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
        elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV11 [HINV12 HINVVALID]]]]]]]]]]]]|idtac|idtac|idtac|idtac|idtac]; clear Heq.
        - and_proof; auto.
          + intros; eapply HINV; eauto.
            rewrite PTree.gsspec; destruct peq; auto.
            subst.
            exploit INV1; eauto.
            intros.
            exploit pred_hyp3; eauto.
            congruence.
          + intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
            rewrite INV3 in H; auto; congruence.
          + intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
          + intros i Hin; destruct Hin; [subst|apply HINV2; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
            unfold erase_instr, get_opt ; simpl.
            rewrite map_map_erase with (f:= (read_gamma g)) ; eauto.
            rewrite erase_reg_pamr; eauto.
            destruct s0 ; simpl ; eauto.
            rewrite erase_reg_pamr; eauto.

          + intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV5;eauto;fail].
            replace (read_gamma gj) with (update (read_gamma g) r df).
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean; in_succ_case; clean.
            destruct s0; simpl; econstructor.
            * intros.  inv H ; try congruence.
              -- rewrite Bij.BIJ1 in H0; eauto. inv H0; auto.
              -- elim list_in_map_inv with (1:= H1); intros xx [V1 V2]; subst.
                 rewrite Bij.BIJ1 in H0; eauto. inv H0; auto.
            * rewrite Bij.BIJ1; eauto. 
            * intros. inv H.
              -- rewrite Bij.BIJ1 in H0; auto. inv H0; eauto.
                 eauto.
              -- inv H1.
                 ++ rewrite Bij.BIJ1 in H0; auto.
                    inv H0; eauto.
                    eauto.
                 ++ apply list_in_map_inv in H; auto.
                    destruct H as [rx [EQ Hin]]. subst.
                    rewrite Bij.BIJ1 in H0; auto. inv H0; eauto.
                    eauto.
            * intros. inv H.
              -- eapply Bij.from_valid_index_to_valid_reg_ssa; eauto. 
              -- inv H0.
                 ++ eapply Bij.from_valid_index_to_valid_reg_ssa; eauto. 
                 ++ apply list_in_map_inv in H; auto.
                    destruct H as [rx [EQ Hin]]. subst.
                    eapply Bij.from_valid_index_to_valid_reg_ssa; eauto. 
                    
            * intros.
              elim list_in_map_inv with (1:= H); intros xx [V1 V2]; subst.
              rewrite Bij.BIJ1 in H0; eauto. inv H0; auto.
            * rewrite Bij.BIJ1; eauto. 
            * intros. inv H.
              -- rewrite Bij.BIJ1 in H0; auto. inv H0; eauto.
                 eauto.
              -- apply list_in_map_inv in H1; auto.
                 destruct H1 as [rx [EQ Hin]]. subst.
                 rewrite Bij.BIJ1 in H0 by eauto; auto.
                 inv H0; eauto.
            * intros. inv H.
              -- eapply Bij.from_valid_index_to_valid_reg_ssa; eauto.
              -- apply list_in_map_inv in H0; auto.
                 destruct H0 as [rx [EQ Hin]]. subst.
                 eapply Bij.from_valid_index_to_valid_reg_ssa; eauto.
            * generalize (HINV _ _ (PTree.gss _ _ _)); intros; clean.
              clean ; in_succ_case ; clean.
              apply extensionality; unfold update; intros; destruct peq; unfold read_gamma.
              subst; rewrite PTree.gss; auto.
              rewrite PTree.gso; auto.
          + intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV3 with i;auto;fail].
            clean; inv Hout.
          + intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV6;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean; in_succ_case; clean.
            exploit pred_hyp3; eauto; intro T; inv T.
          + intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV9; eauto; fail].
            clean; in_succ_case; clean.
            exploit pred_hyp3; eauto; intro T; inv T.
          + intros i ins Hs; elim HINV10 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto. 
          + intros i ins Hs; elim HINV11 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            intros Hss; inv Hss; right; repeat split; try congruence; intros.
            econstructor; eauto.
            rewrite Bij.BIJ1; eauto.
            intros EE; rewrite <- (Pos.eqb_eq xH df) in EE; destruct (Pos.eqb xH df); simpl in *; congruence.
            in_succ_case.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
        - (* PO1 *)
          intros n1 n2 ins g' T1 T2 T3 T4.
          rewrite PTree.gsspec in T1; destruct peq; subst; auto.
          case_eq (is_joinpoint preds n); intros; auto.
          assert (n1=a).
          eapply pred_hyp2; eauto; simpl; auto.
          subst; intuition.
          eauto.
        - (* PO2 *)
          intros j gj dphi H H0 H1 x i H2.
          rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
          exploit pred_hyp3; eauto.
          congruence.
        - (* PO3 *)
          intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
        - (* PO4 *)
          intros.
          rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence; eauto.
          exploit pred_hyp3; eauto; intro T; inv T.
        - (* PO5 *)
          unfold valid_ttgamma. intros.
          destruct (peq pc n).
          + subst. rewrite PTree.gss in H. inv H.
            destruct (peq r x).
            * subst. unfold read_gamma. rewrite PTree.gss.
              eauto.
            * unfold read_gamma. rewrite PTree.gso; auto.
              case_eq (g ! x); auto; intros.
              eapply INVVALID with (pc:= a) (x:= x); eauto.
              unfold read_gamma. rewrite H; auto.
          + rewrite PTree.gso in H; auto. eapply INVVALID; eauto.
      }

    + { (* Itailcall *)
        intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
        inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
        elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV11 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV12 HINVVALID]]]]]]]]]]]]|idtac|idtac|idtac|idtac|idtac]; clear Heq.
        - and_proof; auto. 
          + intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
            rewrite INV3 in H; auto; congruence.
          + intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
          + intros i Hin; destruct Hin; [subst|apply HINV11; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
            unfold erase_instr, get_opt ; simpl.
            rewrite map_map_erase with (f:= (read_gamma g)) ; eauto.
            destruct s0 ; simpl; eauto.
            rewrite erase_reg_pamr; eauto.

          + intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV2;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean; in_succ_case; clean.
          + intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV5 with i;auto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean.
            destruct s0; unfold map_os ; simpl; econstructor.
            * intros. inv H ; try congruence.
              rewrite Bij.BIJ1 in H0 by eauto. inv H0; auto.
              elim list_in_map_inv with (1:= H1); intros xx [V1 V2]; subst.
              rewrite Bij.BIJ1 in H0; eauto. inv H0; auto.
            * intros. inv H.
              -- rewrite Bij.BIJ1 in H0 by eauto. inv H0; eauto. 
              -- apply list_in_map_inv in H1; auto.
                 destruct H1 as [rx [EQ Hin]]. subst.
                 rewrite Bij.BIJ1 in H0 by eauto. inv H0; eauto.
            * intros. inv H.
              -- eapply Bij.from_valid_index_to_valid_reg_ssa; eauto. 
              -- apply list_in_map_inv in H0; auto.
                 destruct H0 as [rx [EQ Hin]]. subst.
                 eapply Bij.from_valid_index_to_valid_reg_ssa; eauto.
                 
            * intros.
              elim list_in_map_inv with (1:= H); intros xx [V1 V2]; subst.
              rewrite Bij.BIJ1 in H0; eauto. inv H0; auto.
            * intros. apply list_in_map_inv in H; auto.
              destruct H as [rx [EQ Hin]]. subst.
              rewrite Bij.BIJ1 in H0 by eauto. inv H0; eauto. 
            * intros. apply list_in_map_inv in H; auto.
              destruct H as [rx [EQ Hin]]. subst.
              eapply Bij.from_valid_index_to_valid_reg_ssa; eauto.
              
              
          + intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV3;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean; in_succ_case; clean.
          + intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV8; eauto; fail].
            clean; in_succ_case; clean.
          + intros i ins Hs; elim HINV9 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto. 
          + intros i ins Hs; elim HINV10 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
            in_succ_case.
        - (* PO1 *)
          intros n1 n2 ins g' T1 T2 T3 T4.
          apply INV1 with n1 ins g'; auto.
        - (* PO2 *)
          eauto.
        - (* PO3 *)
          intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
        - (* PO4 *)
          eauto.
        - (* PO5 *)
          eauto.
      }

    + { (* Ibuiltin *)
        destruct b ; simpl. 
        { case_eq (def ! a); simpl; [intros df Hdef|intro; kill_error].
        case_eq (negb (Pos.eqb 1 df)); [intros Hnp|simpl; kill_error].
        intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
        inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
        elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV11 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV12 HINVVALID]]]]]]]]]]]]|idtac|idtac|idtac|idtac|idtac]; clear Heq.
        - and_proof; auto.
          + intros; eapply HINV; eauto.
            rewrite PTree.gsspec; destruct peq; auto.
            subst.
            exploit INV1; eauto.
            intros.
            exploit pred_hyp3; eauto.
            congruence.
          + intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
            rewrite INV3 in H; auto; congruence.
          + intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
          + intros i Hin; destruct Hin; [subst|apply HINV11; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
            unfold get_opt, erase_instr.
            rewrite list_map_compose.
            rewrite map_map_builtin_arg_id; eauto.
            simpl. unfold erase_reg. rewrite Bij.BIJ1; eauto.
            
          + intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV2;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            replace (read_gamma gj) with (update (read_gamma g) x df).
            clean; in_succ_case; clean.
            constructor; auto.
            * intros.
              eapply in_params_of_builtin_args_erase; eauto.
            * rewrite Bij.BIJ1; eauto.
            * intros. inv H.
              -- rewrite Bij.BIJ1 in H0 by eauto. inv H0; eauto.
              -- eapply in_params_of_builtin_args_valid in H1 ; auto.
                 apply Bij.from_valid_reg_ssa_to_valid_index in H1; auto.
                 rewrite H0 in H1; simpl in H1; auto.
                 eauto.
            * intros. inv H.
              -- eapply Bij.from_valid_index_to_valid_reg_ssa; eauto. 
              -- eapply in_params_of_builtin_args_valid in H0; auto.
                 eauto.
            * clean ; in_succ_case ; clean.
              generalize (HINV _ _ (PTree.gss _ _ _)); intros; clean.
              apply extensionality; unfold update; intros; destruct peq; unfold read_gamma.
              subst; rewrite PTree.gss; auto.
              rewrite PTree.gso; auto.
          + intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV5 with i;auto;fail].
            clean; inv Hout.
          + intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV3;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean; in_succ_case; clean.
            exploit pred_hyp3; eauto; intro T; inv T.
          + intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV8; eauto; fail].
            clean; in_succ_case; clean.
            exploit pred_hyp3; eauto; intro T; inv T.
          + intros i ins Hs; elim HINV9 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto. 
          + intros i ins Hs; elim HINV10 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            intros Hss; inv Hss; right; repeat split; try congruence; intros.
            econstructor; eauto.
            rewrite Bij.BIJ1; eauto. 
            intros EE; rewrite <- (Pos.eqb_eq xH df) in EE; destruct (Pos.eqb xH df); simpl in *; congruence.
            in_succ_case.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
        - (* PO1 *)
          intros n1 n2 ins g' T1 T2 T3 T4.
          rewrite PTree.gsspec in T1; destruct peq; subst; auto.
          case_eq (is_joinpoint preds n); intros; auto.
          assert (n1=a).
          eapply pred_hyp2; eauto; simpl; auto.
          subst; intuition.
          eauto.
        - (* PO2 *)
          intros j gj dphi H H0 H1 xx i H2.
          rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
          exploit pred_hyp3; eauto.
          congruence.
        - (* PO3 *)
          intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
        - (* PO4 *)
          intros.
          rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence; eauto.
          exploit pred_hyp3; eauto; intro T; inv T.
        - (* PO5 *)
          unfold valid_ttgamma. intros.
          destruct (peq pc n).
          + subst. rewrite PTree.gss in H. inv H.
            destruct (peq x0 x).
            * subst. unfold read_gamma. rewrite PTree.gss.
              eauto.
            * unfold read_gamma. rewrite PTree.gso; auto.
              case_eq (g ! x0); auto; intros.
              eapply INVVALID with (pc:= a) (x:= x0); eauto.
              unfold read_gamma. rewrite H; auto.
          + rewrite PTree.gso in H; auto. eapply INVVALID; eauto.
      }
        {
          { intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
        inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
        elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV11 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV12 HINVVALID]]]]]]]]]]]]|idtac|idtac|idtac|idtac|idtac]; clear Heq.
        - and_proof; auto.
          + intros; eapply HINV; eauto.
            rewrite PTree.gsspec; destruct peq; auto.
            subst.
            exploit INV1; eauto.
            intros.
            exploit pred_hyp3; eauto.
            congruence.
          + intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
            rewrite INV3 in H; auto; congruence.
          + intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
          + intros i Hin; destruct Hin; [subst|apply HINV11; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
            unfold erase_instr, get_opt ; simpl.
            rewrite list_map_compose.
            rewrite map_map_builtin_arg_id; eauto.

          + intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV2;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean; in_succ_case; clean.
            { apply wt_Ibuiltin; auto.
              - discriminate.
              - intros.
                eapply in_params_of_builtin_args_erase; eauto.
              - intros.
                apply in_params_of_builtin_args_valid in H; auto.
                apply Bij.from_valid_reg_ssa_to_valid_index in H; auto.
                rewrite H0 in H; simpl in H; auto.
                eauto.
              - intros.
                apply in_params_of_builtin_args_valid in H; auto.
                eauto.
            }
            
          + intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV5 with i;auto;fail].
            clean; inv Hout.
          + intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV3;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean; in_succ_case; clean.
            exploit pred_hyp3; eauto; intro T; inv T.
          + intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV8; eauto; fail].
            clean; in_succ_case; clean.
            exploit pred_hyp3; eauto; intro T; inv T.
          + intros i ins Hs; elim HINV9 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto. 
          + intros i ins Hs; elim HINV10 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            intros Hss; inv Hss; right; repeat split; try congruence; intros.
            eapply wt_eidx_ibuiltin; eauto ; try discriminate.
            clean ; in_succ_case; clean. congruence.
        - (* PO1 *)
          intros n1 n2 ins g' T1 T2 T3 T4.
          rewrite PTree.gsspec in T1; destruct peq; subst; auto.
          case_eq (is_joinpoint preds n); intros; auto.
          assert (n1=a).
          eapply pred_hyp2; eauto; simpl; auto.
          subst; intuition.
          eauto.
        - (* PO2 *)
          intros j gj dphi H H0 H1 xx i H2.
          rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
          exploit pred_hyp3; eauto.
          congruence.
        - (* PO3 *)
          intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
        - (* PO4 *)
          intros.
          rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence; eauto.
          exploit pred_hyp3; eauto; intro T; inv T.
        - (* PO5 *)
          unfold valid_ttgamma. intros.
          destruct (peq pc n).
          + subst. rewrite PTree.gss in H. inv H.
            eauto.
          + rewrite PTree.gso in H; auto.
            eapply INVVALID; eauto.
          }
        }
        + {
            intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
        inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
        elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV11 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV12 HINVVALID]]]]]]]]]]]]|idtac|idtac|idtac|idtac|idtac]; clear Heq.
        - and_proof; auto.
          + intros; eapply HINV; eauto.
            rewrite PTree.gsspec; destruct peq; auto.
            subst.
            exploit INV1; eauto.
            intros.
            exploit pred_hyp3; eauto.
            congruence.
          + intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
            rewrite INV3 in H; auto; congruence.
          + intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
          + intros i Hin; destruct Hin; [subst|apply HINV11; auto; fail].
            rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
            unfold erase_instr, get_opt ; simpl.
            rewrite list_map_compose.
            rewrite map_map_builtin_arg_id; eauto.
            rewrite ! map_builtin_res_id; eauto.
            
          + intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV2;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            
            clean; in_succ_case; clean.
            constructor; auto.
            * discriminate.
            * intros.
              eapply in_params_of_builtin_args_erase; eauto.
            * intros.
              apply in_params_of_builtin_args_valid in H; auto.
              eapply Bij.from_valid_reg_ssa_to_valid_index in H.
              rewrite H0 in H; simpl in H; auto.
              eauto.
            * intros.
              apply in_params_of_builtin_args_valid in H; auto.
              eauto.
              
          + intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV5 with i;auto;fail].
            clean; inv Hout.
          + intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV3;eauto;fail].
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            clean; in_succ_case; clean.
            exploit pred_hyp3; eauto; intro T; inv T.
          + intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV8; eauto; fail].
            clean; in_succ_case; clean.
            exploit pred_hyp3; eauto; intro T; inv T.
          + intros i ins Hs; elim HINV9 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto. 
          + intros i ins Hs; elim HINV10 with (1:=Hs); auto.
            rewrite PTree.gsspec; destruct peq; subst; auto.
            repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
            intros Hss; inv Hss; right; repeat split; try congruence; intros.
            econstructor; eauto.
            discriminate.
            clean ; in_succ_case ; clean.
            congruence.
        - (* PO1 *)
          intros n1 n2 ins g' T1 T2 T3 T4.
          rewrite PTree.gsspec in T1; destruct peq; subst; auto.
          case_eq (is_joinpoint preds n); intros; auto.
          assert (n1=a).
          eapply pred_hyp2; eauto; simpl; auto.
          subst; intuition.
          eauto.
        - (* PO2 *)
          intros j gj dphi H H0 H1 xx i H2.
          rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
          exploit pred_hyp3; eauto.
          congruence.
        - (* PO3 *)
          intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
        - (* PO4 *)
          intros.
          rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence; eauto.
          exploit pred_hyp3; eauto; intro T; inv T.
        - (* PO5 *)
          unfold valid_ttgamma. intros.
          destruct (peq pc n).
          + subst. rewrite PTree.gss in H. inv H.
            eauto.
          + rewrite PTree.gso in H; auto. eapply INVVALID; eauto.
          }
      }

    + (* Icond *)
  intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV11 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV12 HINVVALID]]]]]]]]]]]]|idtac|idtac|idtac|idtac|idtac]; clear Heq.
  and_proof; auto.
  intros; eapply HINV; eauto.
  rewrite PTree.gsspec; destruct peq; auto.
  subst.
  exploit INV1; eauto.
  intros.
  exploit (pred_hyp3 a n0); eauto.
  congruence.
  rewrite PTree.gsspec; destruct peq; auto.
  subst.
  exploit INV1; eauto.
  intros.
  exploit (pred_hyp3 a n); eauto.
  congruence.
  intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in H; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV11; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  unfold erase_instr, get_opt ; simpl.
  rewrite map_map_erase with (f:= (read_gamma g)) ; eauto.
  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV2;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  assert (G'!j=Some g).
    apply HINV.
    rewrite PTree.gsspec; destruct peq; auto.
    rewrite PTree.gss; auto.
  clean.
  econstructor; auto.
  intros.
  elim list_in_map_inv with (1:= H); intros xx [V1 V2]; subst.
  rewrite Bij.BIJ1 in H0; eauto. inv H0. auto.
  { intros.
    apply list_in_map_inv in H; auto.
    destruct H as [rx [EQ Hin]]. subst.
    rewrite Bij.BIJ1 in H0; auto. inv H0; eauto.
    eauto.
  }
  { intros.
    apply list_in_map_inv in H; auto.
    destruct H as [rx [EQ Hin]]. subst.
    apply Bij.from_valid_index_to_valid_reg_ssa; auto.
    eauto.
  }  
  generalize (HINV _ _ (PTree.gss _ _ _)); intros; clean.
  econstructor; auto.
  intros.
  elim list_in_map_inv with (1:= H); intros xx [V1 V2]; subst.
  rewrite Bij.BIJ1 in H0; eauto. inv H0. auto.
  { intros.
    apply list_in_map_inv in H; auto.
    destruct H as [rx [EQ Hin]]. subst.
    rewrite Bij.BIJ1 in H0; auto. inv H0; eauto.
    eauto.
  }
  { intros.
    apply list_in_map_inv in H; auto.
    destruct H as [rx [EQ Hin]]. subst.
    apply Bij.from_valid_index_to_valid_reg_ssa; auto.
    eauto.
  }
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV5 with i;auto;fail].
  clean; inv Hout.
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV3;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  exploit (pred_hyp3 i j); eauto. intro T; inv T.
  exploit (pred_hyp3 i j); eauto; intro T; inv T.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV8; eauto; fail].
  clean; in_succ_case; clean.
  exploit (pred_hyp3 i j); eauto; intro T; inv T.
  exploit (pred_hyp3 i j); eauto; intro T; inv T.
  intros i ins Hs; elim HINV9 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
  in_succ_case.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  rewrite (HINV j g).
  congruence.
  rewrite PTree.gsspec; destruct peq; auto.
  apply PTree.gss; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  generalize (HINV _ _ (PTree.gss _ _ _)); congruence.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  rewrite PTree.gsspec in T1; destruct peq; subst; auto.
  case_eq (is_joinpoint preds n0); intros; auto.
  assert (n1=a).
  eapply pred_hyp2; eauto; simpl; auto.
  subst; intuition.
  rewrite PTree.gsspec in T1; destruct peq; subst; auto.
  case_eq (is_joinpoint preds n); intros; auto.
  assert (n1=a).
  eapply pred_hyp2; eauto; simpl; auto.
  subst; intuition.
  eauto.
  (* PO2 *)
  intros j gj dphi H H0 H1 x i H2.
  rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
  exploit (pred_hyp3 a n0); eauto.
  congruence.
  rewrite PTree.gsspec in H; destruct peq; [subst|eauto].
  exploit (pred_hyp3 a n); eauto.
  congruence.
  (* PO3 *)
  intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  intros.
  rewrite PTree.gsspec in H0; destruct peq; subst; simpl; try congruence.
  exploit (pred_hyp3 a n0); eauto; intro T; inv T.
  rewrite PTree.gsspec in H0; destruct peq; subst; simpl; eauto.
  exploit (pred_hyp3 a n); eauto; intro T; inv T.
  (* PO5 *)
  { unfold valid_ttgamma. intros.
    destruct (peq n0 pc).
    - subst. unfold read_gamma. rewrite PTree.gss in H. inv H.
      case_eq (g0 ! x); auto; intros.
      eapply INVVALID with (pc:= a) (x:= x); eauto.
      unfold read_gamma. rewrite H; auto.
    - rewrite PTree.gso in H; auto.
      destruct (peq pc n).
      + subst. unfold read_gamma. rewrite PTree.gss in H. inv H.
        case_eq (g0 ! x); auto; intros.
        eapply INVVALID with (pc:= a) (x:= x); eauto.
        unfold read_gamma. rewrite H; auto.
      + rewrite PTree.gso in H; eauto.
  }
    + (* Ijumptable *)
  intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV11 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV12 HINVVALID]]]]]]]]]]]]|idtac|idtac|idtac|idtac|idtac]; clear Heq.
  and_proof; auto.
  intros; eapply HINV; eauto.
  elim upd_list_some with l g G n; destruct 1; auto.
  exploit INV1; eauto.
  intros.
  exploit (pred_hyp3 a n); eauto.
  congruence.
  rewrite H1; auto.
  intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in H; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV11; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  unfold get_opt, erase_instr. simpl.
  unfold erase_reg. rewrite Bij.BIJ1; eauto.
  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV2;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  assert (G'!j=Some g).
    apply HINV.
    elim upd_list_some with l g G j; destruct 1; intuition.
  clean.
  econstructor; auto.
  intros. inv H.
  rewrite Bij.BIJ1 in H0 by eauto. inv H0 ; auto.
  inv H1.
  { intros.
    inv H.
    - rewrite Bij.BIJ1 in H0 by eauto. 
      inv H0; eauto. 
    - inv H1.
  }
  { intros.
    inv H.
    - apply Bij.from_valid_index_to_valid_reg_ssa; eauto. 
    - inv H0.
  }
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV5 with i;auto;fail].  
  clean; inv Hout.
  assert (G!i = Some gi).
    simpl in HINV.
    rewrite (HINV _ g) in Hgi; congruence.
  rewrite H in Hg; inv Hg.
  econstructor; auto.
  intros ; inv H0 ; inv H1 ; auto.
  rewrite Bij.BIJ1 in H2 by eauto. inv H2. auto.
  inv H2.
  { intros.
    inv H0.
    - rewrite Bij.BIJ1 in H1 by eauto; auto.
      inv H1; eauto.      
    - inv H2.
  }
  { intros.
    inv H0.
    - apply Bij.from_valid_index_to_valid_reg_ssa; auto.
      eauto.
    - inv H1.
  }
  
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV3;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  exploit pred_hyp3; eauto; intro T; inv T.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV8; eauto; fail].
  clean; in_succ_case; clean.
  exploit pred_hyp3; eauto; intro T; inv T.
  intros i ins Hs; elim HINV9 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
  in_succ_case.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  rewrite (HINV j g).
  congruence.
  elim upd_list_some with l g G j; destruct 1; intuition.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  elim upd_list_some with l g G n2; destruct 1; auto.
  case_eq (is_joinpoint preds n2); intros; auto.
  assert (n1=a).
  eapply pred_hyp2; eauto; simpl; auto.
  subst; intuition.
  rewrite H0 in *; eauto.
  (* PO2 *)
  intros j gj dphi H H0 H1 x i H2.
  elim upd_list_some with l g G j; destruct 1; auto.
  exploit pred_hyp3; eauto.
  congruence.
  rewrite H4 in *; eauto.
  (* PO3 *)
  intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  intros.
  elim upd_list_some with l g G i; destruct 1; auto.
  exploit pred_hyp3; eauto; intro T; inv T.
  rewrite H2 in H0; eauto.
  (* PO5 *)
  eapply upd_list_valid_ttgamma; eauto.
  
  + (* Ireturn *)
  case_eq o; [intros oa Ho|intros Ho].
  intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV11 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV12 HINVVALID]]]]]]]]]]]]|idtac|idtac|idtac|idtac|idtac]; clear Heq.
  and_proof; auto.
  intros.
  intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in H; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV11; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  unfold erase_instr, get_opt ; simpl.
  unfold erase_reg. rewrite Bij.BIJ1; eauto.
  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV2;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV5 with i;auto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean.
  econstructor; auto.
  intros. inv H ; inv H0 ; auto.
  rewrite Bij.BIJ1 in H1; eauto. inv H1. auto.
  inv H1.
  { intros.
    inv H.
    - rewrite Bij.BIJ1 in H0 by eauto. inv H0; eauto. 
    - inv H1.
  }
  { intros.
    inv H.
    - apply Bij.from_valid_index_to_valid_reg_ssa; auto.
      eauto.
    - inv H0.
  }  
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV3;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV8; eauto; fail].
  clean; in_succ_case; clean.
  intros i ins Hs; elim HINV9 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
  in_succ_case.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  eauto.
  (* PO2 *)
  eauto.
  (* PO3 *)
  intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  intros.
  eauto.
  (* PO5 *)
  eauto.
  
  intros Heq Hln INV1 INV2 INV3 INV4 INVVALID.
  inversion Hln as [|a' l' Hln1 Hln2]; subst; clear Hln.
  elim IHppoints with (1:=Heq) (2:=Hln2); [intros HINV [HINV1 [HINV4 [HINV11 [HINV2 [HINV5 [HINV3 [HINV6 [HINV7 [HINV8 [HINV9 [HINV10 [HINV12 HINVVALID]]]]]]]]]]]]|idtac|idtac|idtac|idtac|idtac]; clear Heq.
  and_proof; auto.
  intros.
  intros; apply HINV1; rewrite PTree.gsspec; destruct peq; subst; auto.
  rewrite INV3 in H; auto; congruence.
  intros i Hin; destruct Hin; [subst|apply HINV4; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  intros i Hin; destruct Hin; [subst|apply HINV11; auto; fail].
  rewrite (HINV1 _ _ (PTree.gss _ _ _)); rewrite Hins; auto.
  unfold erase_instr, get_opt ; simpl.
  intros i j ins gi gj Hin Hsucc1 Hsucc2 Hgi Hgj Hjun; destruct Hin; [subst|eapply HINV2;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  intros i ins gi Hin Hcode Hout Hgi; destruct Hin; [subst|apply HINV5 with i;auto;fail].
  clean.
  econstructor; auto.
  intros i j ins gi gj dpi Hin Hsucc1 Hsucc2 Hgi Hgj Hjun Hdefphi; destruct Hin; [subst|eapply HINV3;eauto;fail].
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  clean; in_succ_case; clean.
  intros i j ins Hin Hsucc1 Hsucc2 Hjun; destruct Hin; [subst|eapply HINV8; eauto; fail].
  clean; in_succ_case; clean.
  intros i ins Hs; elim HINV9 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto. 
  intros i ins Hs; elim HINV10 with (1:=Hs); auto.
  rewrite PTree.gsspec; destruct peq; subst; auto.
  repeat match goal with id: G! _ = Some _ |- _ => generalize (Pr _ _ id); clear id; intros id end.
  intros Hss; inv Hss; right; repeat split; try congruence; try constructor; intros.
  in_succ_case.
  (* PO1 *)
  intros n1 n2 ins g' T1 T2 T3 T4.
  eauto.
  (* PO2 *)
  eauto.
  (* PO3 *)
  intros i Hn; rewrite PTree.gsspec; destruct peq; subst; intuition.
  (* PO4 *)
  eauto.
  (* PO5 *)
  eauto.  
Qed.

End fold_left_update_ctx_prop.


(** * Properties about [normalised_function] *)
Lemma normalised_entry_not_successor : forall f ins i,
  normalised_function f ->
  (RTLdfs.fn_code f)!i = Some ins ->
  In (RTLdfs.fn_entrypoint f) (RTLdfs.successors_instr ins) -> False.
Proof.
  unfold normalised_function; intros.
  exploit check_function_inv_correct01; eauto.
Qed.

Lemma normalised_entry_not_joinpoint : forall f,
  normalised_function f ->
  ~ is_joinpoint (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) (RTLdfs.fn_entrypoint f) = true.
Proof.
  red; unfold normalised_function; intros.
  exploit check_function_inv_correct12; eauto.
  rewrite is_joinpoint_iff_join_point; auto.
Qed.

Lemma assigned_fold_Iphi_map : forall (pred:list node) (live:Registers.reg->bool) f g (d:PTree.t index)
  args dst,
  In (Iphi args dst)
  (PTree.fold
    (fun phis x xdef =>
      if live x
        then Iphi (map (f x) pred) (g x xdef) :: phis
        else phis) d nil) -> 
  exists x, exists xdef, d!x = Some xdef /\
    args = map (f x) pred /\ dst = g x xdef /\ live x = true.

Proof.
  intros pred live f g d.
  apply (@PTree_Properties.fold_rec _ _ 
    (fun phis x xdef =>
      if live x
        then Iphi (map (f x) pred) (g x xdef) :: phis
        else phis)
    (fun d phis => forall args dst,
      In (Iphi args dst) phis -> 
      exists x, exists xdef, d!x = Some xdef /\
        args = map (f x) pred /\ dst = g x xdef /\ live x = true) nil d).
  intros m m' phis He H args dst Hi.
  elim H with (1:=Hi); intros x [xdef [Hx1 Hx2]].
  rewrite He in Hx1; eauto.
  simpl; intuition.
  intros m a k v Hm1 Hm2 Hm3 args dst.
  case_eq (live k); intros.
  simpl in H0; destruct H0.
  inv H0.
  exists k; exists v.
  rewrite PTree.gss; auto.
  elim Hm3 with (1:=H0); intros x [xdef [Hx1 Hx2]].
  exists x; exists xdef; split; auto.
  rewrite PTree.gso; auto.
  intro; congruence.
  elim Hm3 with (1:=H0); intros x [xdef [Hx1 Hx2]].
  exists x; exists xdef; split; auto.
  rewrite PTree.gso; auto.
  intro; congruence.
Qed.

Lemma assigned_fold_Iphi_map2 : forall (pred:list node) (live:Registers.reg->bool) f g (d:PTree.t index)
  x xdef,
  d!x = Some xdef -> live x = true ->
  In (Iphi (map (f x) pred) (g x xdef))
  (PTree.fold
    (fun phis x xdef =>
      if live x
        then Iphi (map (f x) pred) (g x xdef) :: phis
        else phis) d nil).
Proof.
  intros pred live f g d.
  apply (@PTree_Properties.fold_rec _ _ 
    (fun phis x xdef =>
      if live x
        then Iphi (map (f x) pred) (g x xdef) :: phis
        else phis)
    (fun d phis => forall x xdef,
      d!x = Some xdef -> live x = true ->
      In (Iphi (map (f x) pred) (g x xdef)) phis)).
  intros m m' phis He H args dst Hi.
  rewrite <- He in Hi; eauto.
  intros; rewrite PTree.gempty in *; congruence.
  intros m a k v Hm1 Hm2 Hm3 x xdef.
  case_eq (live k); intros.
  rewrite PTree.gsspec in H0; destruct peq; subst.
  left; congruence.
  right; eauto.
  rewrite PTree.gso in H0; eauto.
  intro; congruence.
Qed.


Lemma In_Iphi_fold1: forall size (l:list positive) f (g:positive->bool) args dst d1 d2,
  In (Iphi args dst)
  (PTree.fold
    (fun phis (x xdef:positive) =>
      if g x then Iphi (map (f x) l) (Bij.pamr size (x, xdef)) :: phis
        else phis) d1 d2) -> List.length l = List.length args \/ In (Iphi args dst) d2.
Proof.
  intros size l f g args dst d1 d2.
  apply PTree_Properties.fold_rec with
    (P:=fun m d3 => In (Iphi args dst) d3 -> List.length l = List.length args \/ In (Iphi args dst) d2); auto.
  intros.
  destruct (g k); auto.
  destruct H2; auto.
  inv H2; left.
  rewrite list_length_map; auto.
Qed.

Lemma In_Iphi_fold1': forall size (l:list positive) f (g:positive->bool) args dst d1,
  In (Iphi args dst)
  (PTree.fold
    (fun phis (x xdef:positive) =>
      if g x then Iphi (map (f x) l) (Bij.pamr size (x, xdef)) :: phis
        else phis) d1 nil) -> List.length l = List.length args.
Proof.
  intros.
  exploit In_Iphi_fold1; eauto.
  destruct 1; auto.
  elim H0.
Qed.

Lemma In_Iphi_fold2: forall size (l:list positive) f (g:positive->bool) args dst d1,
  In (Iphi args dst)
  (PTree.fold
    (fun phis (x xdef:positive) =>
      if g x then Iphi (map (f x) l) (Bij.pamr size (x, xdef)) :: phis
        else phis) d1 nil) -> 
  forall k, nth_okp k l -> nth_okp k args.
Proof.
  intros.
  exploit In_Iphi_fold1; eauto.
  destruct 1; auto.
  eapply nth_okp_length; eauto.
  inv H1.
Qed.

Lemma In_Iphi_fold4: forall size (l:list positive) (f: positive -> positive -> Bij.index) (g:positive->bool) args dst dst' args' d1 d2,
    forall (VALID: forall x, In x d1 -> Bij.valid_index size (snd x) = true),
    In (Iphi args dst)
    (fold_left
      (fun phis x =>
         if g (fst x)
         then  Iphi (map (fun pc => Bij.pamr size (fst x,f (fst x) pc)) l) (Bij.pamr size (fst x,snd x)) :: phis
         else phis) d1 d2) ->
    In (Iphi args' dst')
    (fold_left
      (fun phis x =>
        if g (fst x) then Iphi (map (fun pc => Bij.pamr size (fst x,f (fst x) pc)) l) (Bij.pamr size (fst x,snd x)) :: phis
          else phis) d1 d2) ->
    (forall args dst args' dst', In (Iphi args dst) d2 -> In (Iphi args' dst') d2 -> fst (Bij.rmap size dst) = fst (Bij.rmap size dst') -> dst = dst' /\ args=args') ->
    (forall args dst , In (Iphi args dst) d2 -> ~ In (fst (Bij.rmap size dst)) (List.map (@fst _ _) d1)) ->
    list_norepet (List.map (@fst _ _) d1) ->
    fst (Bij.rmap size dst) = fst (Bij.rmap size dst') -> dst = dst' /\ args = args'.
Proof.
  induction d1; simpl; intros.
  eauto.
  inv H3.
  eapply IHd1; eauto.
  - intros.
    destruct (g (fst a)); eauto.
    simpl in *; destruct H3; destruct H5.
    + inv H3; inv H5; auto.
    + inv H3.
      elim (H2 _ _ H5); auto.
      rewrite Bij.BIJ1 in H6; auto.
    + inv H5.
      elim (H2 _ _ H3); auto.
      rewrite Bij.BIJ1 in H6; auto.
    + eauto.
  - intros.
    destruct (g (fst a)).
    simpl in H3; destruct H3.
    inv H3; auto.
    rewrite Bij.BIJ1; auto. 
    intro; elim H2 with (1:=H3); auto.
    intro; elim H2 with (1:=H3); auto.
Qed.

Lemma In_Iphi_fold5: forall size (l:list positive) f (g:positive->bool) args dst dst' args' d1,
    forall (VALID: forall x, In x (PTree.elements d1) -> Bij.valid_index size (snd x) = true),
    In (Iphi args dst)
    (PTree.fold
      (fun phis (x xdef:positive) =>
        if g x then Iphi (map (fun pc => Bij.pamr size (x,f x pc)) l) (Bij.pamr size (x, xdef)) :: phis
          else phis) d1 nil) ->
    In (Iphi args' dst')
    (PTree.fold
      (fun phis (x xdef:positive) =>
        if g x then Iphi (map (fun pc => Bij.pamr size (x,f x pc)) l) (Bij.pamr size (x, xdef)) :: phis
          else phis) d1 nil) ->
    fst (Bij.rmap size dst) = fst (Bij.rmap size dst') -> dst = dst' /\ args = args'.
Proof.
  intros size l f g args dst dst' args' d1.
  rewrite PTree.fold_spec; intros.
  eapply (In_Iphi_fold4 size l f g) ; eauto.
  - intros. elim H2.
  - apply PTree.elements_keys_norepet.
Qed.

Lemma In_Iphi_fold7: forall size (l:list positive) f (g:positive->bool) d1 args dst args' dst',
    forall (VALID: forall x, In x (PTree.elements d1) -> Bij.valid_index size (snd x) = true),
    In (Iphi args dst) (PTree.fold
      (fun phis (x xdef:positive) =>
        if g x then Iphi (map (fun pc => Bij.pamr size (x,f x pc)) l) (Bij.pamr size (x, xdef)) :: phis
          else phis) d1 nil) -> 
    In (Iphi args' dst') (PTree.fold
      (fun phis (x xdef:positive) =>
        if g x then Iphi (map (fun pc => Bij.pamr size (x,f x pc)) l) (Bij.pamr size (x, xdef)) :: phis
          else phis) d1 nil) ->
    (args <> args' \/ dst <> dst') ->
    (erase_reg size dst) <> (erase_reg size dst').
Proof.
  intros; intro.
  elim (In_Iphi_fold5 _ _ _ _ _ _ _ _ _  VALID H H0); auto.
  destruct H1; intuition.
Qed.

Lemma aux_same_succ : forall l rtl_code code,
  (∀ (j : positive) (ins : RTL.instruction),
         rtl_code ! j = Some ins → In j l) ->
  (∀ i : node,
       In i l
       → get_opt successors_instr code ! i =
         get_opt RTLdfs.successors_instr rtl_code ! i) ->
  (∀ (i : positive) (ins : instruction),
       code ! i = Some ins
       → In i l ∨ (PTree.empty instruction) ! i = Some ins) ->
  forall i:node, 
    (PTree.map1 RTLdfs.successors_instr rtl_code)!i = 
    (PTree.map1 successors_instr code)!i.
Proof.
  intros l rtl_code code T H1 H9 i1.
  repeat rewrite PTree.gmap1.
  case_eq (rtl_code!i1); intros.
  - exploit (H1 i1).
    eapply T; eauto.
    rewrite H.
    simpl.
    destruct (code!i1); simpl; auto.
  - case_eq (code!i1); intros.
    * simpl in *.
      exploit H9; eauto.
      destruct 1.
      exploit (H1 i1) ;eauto.
      rewrite H; rewrite H0; simpl; try congruence.
      rewrite PTree.gempty in *; congruence.
    * auto.
Qed.


Require Import RTLdfsproof.
  
(** * The typechercker [typecheck_function] satisfies its specification *)
Theorem typecheck_function_correct : forall f size def def_phi live f_ssa,
    (forall j ins, (RTLdfs.fn_code f)!j = Some ins -> In j (fn_dfs f)) -> 
    list_norepet (fn_dfs f) -> 
    typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK f_ssa ->
    exists G,
      wt_function size f f_ssa live G
      /\ wf_init size f_ssa G
      /\ check_erased_spec size f f_ssa
      /\ normalised_function f 
      /\ (check_phi_params_spec f_ssa /\ check_no_duplicates_spec size f_ssa)
      /\ (forall pc block, (fn_phicode f_ssa) ! pc = Some block ->  exists ins, (fn_code f_ssa) ! pc = Some ins)
      /\ (forall pc, RTLutils.join_point pc f <-> join_point pc f_ssa)
      /\ (forall phib jp i, (fn_code f_ssa) ! jp = Some i
                            -> (fn_phicode f_ssa) ! jp = Some phib
                            -> join_point jp f_ssa)
      /\ (forall phib jp, (fn_phicode f_ssa) ! jp = Some phib ->
                          forall args dst, In (Iphi args dst) phib -> List.length args = List.length ((make_predecessors (fn_code f_ssa) successors_instr) !!! jp))
      /\ (forall phib jp i, f_ssa.(fn_code) ! jp = Some i -> f_ssa.(fn_phicode) ! jp = Some phib -> join_point jp f_ssa)
      /\ (forall jp i, join_point jp f_ssa ->  f_ssa.(fn_code) ! jp = Some i -> 
                         exists phib, f_ssa.(fn_phicode) ! jp = Some phib)
      /\ (forall i, get_opt (erase_instr size) ((f_ssa.(fn_code))!i) = get_opt (fun x => x) ((f.(RTLdfs.fn_code))!i))
.
Proof.
  unfold typecheck_function; intros f size def def_phi live f_ssa HDFS HNOREPET.
  case_eq (Bij.valid_index size dft_pos) ; intros HVALID_dft; try congruence.
  case_eq (check_valid_index size def && check_valid_index_phis size def_phi); intros CHECK_VALID; try congruence.
  case_eq (check_function_inv f (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr)); intros Hcheck; try congruence.
  assert (Hnl:normalised_function f) by (apply Hcheck).
  match goal with |- context[fold_left ?f ?l ?x] => 
                  case_eq (fold_left f l x); 
                    [intros ((G,new_code),jpoints) Hf|simpl; intros; congruence]
  end.
  match goal with |- context[fold_left ?f ?l ?x] => 
                  case_eq (fold_left f l x); simpl;
                    [intros phiblock Hphi|intros; congruence]
  end.
  match goal with |- context[compute_test_dom ?e ?c] =>
                  case_eq (compute_test_dom e c) ; simpl ;
                    [intros domtest Hdom | intros ; congruence]
  end.
  match goal with |- context[check_unique_def ?x] => 
                  case_eq (check_unique_def x); simpl;
                    [intros Hcu|intros; congruence]
  end.
  match goal with |- context[check_code_at_phipoints ?x] => 
                  case_eq (check_code_at_phipoints x); simpl;
                    [intros Hcap|intros; congruence]
  end.
  intros Hok.
  inv Hok; simpl in *.
  exploit fold_left_update_ctx_prop; eauto.

  - intros n1 n2 n' ins1 ins2 H H0 H1 H2 H3.
    assert (~ RTLutils.join_point n' f).
    intro.
    rewrite is_joinpoint_iff_join_point in H4.
    congruence.
    destruct (peq n1 n2); auto.
    elim H4; clear H4 H3.
    assert (In n' ((RTLdfs.successors_map f) !!! n1)).
    unfold successors_list.
    unfold RTLdfs.successors_map; rewrite PTree.gmap1; rewrite H; simpl; auto.
    assert (In n' ((RTLdfs.successors_map f) !!! n2)).
    unfold successors_list.
    unfold RTLdfs.successors_map; rewrite PTree.gmap1; rewrite H1; simpl; auto.
    exploit @make_predecessors_correct_1; eauto. 
    generalize H1 ; clear H1.
    exploit @make_predecessors_correct_1; eauto. 
    intros T3 H1 T4.
    unfold successors_list in *.
    case_eq ((make_predecessors (RTLdfs.fn_code f) RTL.successors_instr)!n'); intros.
    rewrite H5 in *.
    econstructor; eauto.
    destruct l; simpl in *.
    intuition.
    destruct l; simpl in *.
    intuition subst.
    intuition.
    simpl; lia.
    rewrite H5 in *.
    elim T3.

  - intros i j ins Hp Hp0 Hp1.
    rewrite <- is_joinpoint_iff_join_point in Hp1.
    assert (In j (RTLdfs.successors_map f) !!! i).
    unfold successors_list.
    unfold RTLdfs.successors_map; rewrite PTree.gmap1; rewrite Hp; simpl; auto.    
    exploit check_function_inv_correct0; eauto.
    intros [ins' Hi'].
    rewrite (check_function_inv_correct3 _ Hnl _ _ ins' Hp1 H) in Hp; auto.
    congruence.

  - boolInv.
    eapply check_valid_index_correct; eauto.

  - boolInv.
    eapply check_valid_index_phis_correct; eauto.

  - intros n1 n2 ins g Hsome Hin Hsucc1 Hsucc2.
    unfold entry_Gamma in *.
    rewrite PTree.gsspec in Hsome; destruct peq; subst.
    elim normalised_entry_not_successor with f ins n1; auto.
    rewrite PTree.gempty in *; congruence.

  - intros j gj dphi Hsucc1 Hjun Hd xx i Hx.
    unfold entry_Gamma in *.
    rewrite PTree.gsspec in Hsucc1; destruct peq; subst.
    elim normalised_entry_not_joinpoint with f; auto.
    intros.
    rewrite PTree.gempty in *; congruence.

  - intros; rewrite PTree.gempty in *; congruence.

  - intros i g Hj Hsome.
    unfold entry_Gamma in *.
    rewrite PTree.gsspec in Hsome; destruct peq; subst.
    elim normalised_entry_not_joinpoint with f; auto.
    rewrite PTree.gempty in *; congruence.

  - unfold valid_ttgamma, entry_Gamma, read_gamma.
    intros.
    rewrite PTree.gsspec in H; destruct peq; subst.
    + inv H. rewrite PTree.gempty; auto.
    + inv H. rewrite PTree.gempty in H1.
      congruence.
      
  - intros [H [H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 HVALID]]]]]]]]]]]]].
    simpl.
    exists (fun n => match G!n with None => fun _ => xH | Some g => read_gamma g end); split. 
    + constructor; simpl; intros.
      * inv H12; simpl in *.
        { elim H10 with i instr; auto.
          - rewrite PTree.gempty; congruence.
          - intros [T1 [T3 T2]]; generalize (T2 _ H14); clear T2; intros T2.
            assert (HI: In i (fn_dfs f)).
            { elim H9 with i instr; auto.
              rewrite PTree.gempty; congruence.
            }
            assert (He: exists ins', (RTLdfs.fn_code f)!i = Some ins').
            { exploit H1; eauto.
              rewrite H13; simpl.
              case_eq ((RTLdfs.fn_code f)!i); simpl.
              - intros ins0; exists ins0; auto.
              - congruence.    
            }
            destruct He as [instr' He].
            case_eq (is_joinpoint (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) j); intros Hj.
            + exploit (H8 i j instr'); eauto.
              * exploit H1; eauto.
                rewrite H13; rewrite He; simpl; intros.
                inv H12; auto.
              * intros HInj.
                exploit fold_build_phi_block_correct; eauto. intros [_ [HT _]].
                elim HT with j; auto; intros phi Hphi0.
                { econstructor 2; eauto.
                  - econstructor 1; simpl; eauto.
                  - (* wt_eidx *)
                    simpl.
                    assert (HG: (entry_Gamma f) ! (RTLdfs.fn_entrypoint f) = Some (PTree.empty index)).
                    unfold entry_Gamma.
                    rewrite PTree.gss; auto.    
                    rewrite (H _ _ HG).
                    replace (read_gamma (PTree.empty index)) with (fun _ : Registers.reg => 1%positive); auto.
                    apply extensionality.
                    intros; unfold read_gamma; simpl; rewrite PTree.gempty; auto.
                  - (* wt_ephi *) 
                    case_eq (G!i); [intros gi Hgi| intuition;fail].
                    case_eq (G!j); [intros gj Hgj| intuition;fail].
                    exploit fold_build_phi_block_def_phi_some; eauto; intros [d [Hd Hd2]]; eauto.
                    simpl.
                    assert (HG: (entry_Gamma f) ! (RTLdfs.fn_entrypoint f) = Some (PTree.empty index)).
                    unfold entry_Gamma.
                    rewrite PTree.gss; auto.    
                    rewrite (H _ _ HG).
                    replace (read_gamma (PTree.empty index)) with (fun _ : Registers.reg => 1%positive).
                    case_eq ((make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) ! j); eauto.
                    intros pred Hpred.
                    exploit fold_build_phi_block_value; eauto.
                    rewrite Hphi0; intros T.
                    inv T.
                    constructor.
                    intros ri' r i' Has.
                    inv Has.
                    destruct (assigned_fold_Iphi_map _ _ _ _ _ _ _ H12) as [r' [idx [R1 [R2 [R3 R4]]]]].
                    intros; subst.
                    rewrite Bij.BIJ1 in H15; auto. inv H15.
                    generalize (Hd2 _ _ R1); auto.
                    boolInv.
                    eapply check_valid_index_phis_correct; eauto.
                    unfold is_joinpoint in *.
                    intros T; rewrite T in *; congruence.
                    apply extensionality.
                    intros; unfold read_gamma; simpl; rewrite PTree.gempty; auto.

                  - simpl; constructor; simpl.
                    + case_eq (G!i); [intros gi Hgi| intuition;fail].
                      case_eq (G!j); [intros gj Hgj| intuition;fail].
                      exploit fold_build_phi_block_def_phi_some; eauto; intros [d [Hd _]]; eauto.
                      exploit H5; eauto; intros [T4 _].
                      unfold is_joinpoint in *.
                      case_eq ((make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) ! j); eauto.
                      * intros pred Hpred.
                        exploit fold_build_phi_block_value; eauto.
                        rewrite Hphi0; intros T.
                        inv T.
                        intros ri' r i' Has.
                        inv Has.
                        destruct (assigned_fold_Iphi_map _ _ _ _ _ _ _ H12) as [r' [idx [R1 [R2 [R3 R4]]]]].
                        subst; clear H12.
                        rewrite Bij.BIJ1; auto.
                        intros T; inv T.
                        eauto.
                        boolInv.
                        eapply check_valid_index_phis_correct; eauto.
                      * intros Hjunc.
                        rewrite Hjunc in *; congruence.

                    + intros ri r i0 Ha Hb.    
                      destruct Ha as [xx X].
                      case_eq ((make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) ! j); 
                        [intros pred Hpred| intros Hpred; unfold is_joinpoint in Hj; rewrite Hpred in Hj; congruence].
                      exploit fold_build_phi_block_def_phi_some; eauto; intros [d [Hd _]]; eauto.
                      exploit fold_build_phi_block_value; eauto.
                      intros Hp; rewrite Hphi0 in Hp; inv Hp.
                      destruct (assigned_fold_Iphi_map _ _ _ _ _ _ _ X) as [x' [xdef [D1 [D2 [D3 D4]]]]] ; subst.
                      rewrite Bij.BIJ1 in Hb. inv Hb.
                      boolInv; eapply check_valid_index_phis_correct; eauto.
                      boolInv; eapply check_valid_index_phis_correct; eauto.

                      + intros ri Ha.    
                      destruct Ha as [xx X].
                      case_eq ((make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) ! j); 
                        [intros pred Hpred| intros Hpred; unfold is_joinpoint in Hj; rewrite Hpred in Hj; congruence].
                      exploit fold_build_phi_block_def_phi_some; eauto; intros [d [Hd _]]; eauto.
                      exploit fold_build_phi_block_value; eauto.
                      intros Hp; rewrite Hphi0 in Hp; inv Hp.
                      destruct (assigned_fold_Iphi_map _ _ _ _ _ _ _ X) as [x' [xdef [D1 [D2 [D3 D4]]]]] ; subst.
                      apply Bij.from_valid_index_to_valid_reg_ssa; auto.
                      boolInv; eapply check_valid_index_phis_correct; eauto.

                    + intros ri r i0 Ha Hb.    
                      destruct Ha as [xx X].
                      case_eq ((make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) ! j); 
                        [intros pred Hpred| intros Hpred; unfold is_joinpoint in Hj; rewrite Hpred in Hj; congruence].
                      exploit fold_build_phi_block_def_phi_some; eauto; intros [d [Hd _]]; eauto.
                      exploit fold_build_phi_block_value; eauto.
                      intros Hp; rewrite Hphi0 in Hp; inv Hp.
                      destruct (assigned_fold_Iphi_map _ _ _ _ _ _ _ X) as [x' [xdef [D1 [D2 [D3 D4]]]]] ; subst.
                      rewrite Bij.BIJ1 in Hb. inv Hb.
                      apply Regset.mem_2; auto.
                      boolInv; eapply check_valid_index_phis_correct; eauto.
                      
                    + intros r Hri.
                      case_eq (G!i); [intros gi Hgi| intuition;fail].
                      case_eq (G!j); [intros gj Hgj| intuition;fail].
                      exploit fold_build_phi_block_def_phi_some; eauto; intros [d [Hd _]]; eauto.
                      exploit H5; eauto; intros [_ T4].
                      unfold is_joinpoint in *.
                      case_eq ((make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) ! j); eauto.
                      intros pred Hpred.
                      exploit fold_build_phi_block_value; eauto.
                      rewrite Hphi0; intros T.
                      inv T.
                      unfold assigned in Hri.
                      case_eq (Regset.mem r (Lin f j (Lout live))); intros Hrm; [left|right].
                      symmetry; apply T4; auto.
                      case_eq (d!r); auto; intros rdef Hrdef.
                      elim Hri with (Bij.pamr size (r,rdef)) rdef.
                      apply Bij.BIJ1.
                      boolInv; eapply check_valid_index_phis_correct; eauto.
                      econstructor; apply assigned_fold_Iphi_map2 with
                                        (f:=fun x pc => Bij.pamr size (x, read_gamma
                                                              match G ! pc with
                                                              | Some m => m
                                                              | None => PTree.empty index
                                                              end x))
                                        (g:=fun x xdef => (Bij.pamr size (x, xdef))); eauto.
                      intros Ti; exploit Regset.mem_1; eauto.
                      intros; congruence.
                      intros Hjj; rewrite Hjj in Hj; congruence.

                  - constructor; simpl.
                    intros args dst r i0 Hi Hb.
                    set (ff:={|
                               fn_sig := RTLdfs.fn_sig f;
                               fn_params := map (fun r0 => Bij.pamr size (r0, dft_pos))
                                                (RTLdfs.fn_params f);
                               fn_stacksize := RTLdfs.fn_stacksize f;
                               fn_code := new_code;
                               fn_phicode := phiblock;
                               fn_entrypoint := RTLdfs.fn_entrypoint f;
                               fn_ext_params := ext_params_list new_code phiblock (map (λ r : Registers.reg, Bij.pamr size (r, dft_pos)) (RTLdfs.fn_params f));
                               fn_dom_test := domtest
                             |}).
                    exploit fold_build_phi_block_def_phi_some; eauto; intros [d [Hd _]]; eauto.
                    unfold is_joinpoint in *.
                    case_eq ((make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) ! j); eauto.
                    intros pred Hpred.
                    exploit fold_build_phi_block_value; eauto.
                    rewrite Hphi0; intros T; inv T.
                    
                    destruct (assigned_fold_Iphi_map _ _ _ _ _ _ _ Hi) as [r' [idx [R1 [R2 [R3 R4]]]]].
                    subst. clear Hi.
                    rewrite Bij.BIJ1 in Hb. inv Hb. 
                    assert (forall i, (RTLdfs.successors_map f) !i = (successors ff) !i)
                      by (eapply aux_same_succ; eauto).                    
                    replace ((make_predecessors new_code successors_instr) !!!j) with pred.
                    clear Hpred Hphi0.
                    + induction pred; simpl.
                      * constructor; auto.
                      * destruct (G!a) eqn:EQ; simpl; auto;
                         [ destruct (t!r) eqn:EQ'; simpl; auto|].
                        -- eapply phiu_cons with (i:= read_gamma t r); auto.
                           rewrite Bij.BIJ1; eauto.
                           eauto.
                           eapply Bij.from_valid_index_to_valid_reg_ssa; eauto.
                        -- unfold read_gamma. rewrite EQ'.
                           eapply phiu_cons with (i:= dft_pos); auto.
                           rewrite Bij.BIJ1; auto.
                           eapply Bij.from_valid_index_to_valid_reg_ssa; eauto.
                           rewrite EQ'; auto.
                        -- unfold read_gamma. rewrite PTree.gempty.
                           eapply phiu_cons with (i:= dft_pos); auto.
                           rewrite Bij.BIJ1; auto.
                           eapply Bij.from_valid_index_to_valid_reg_ssa; eauto.
                    + unfold successors_list.
                      erewrite <- (same_successors_same_predecessors _ _ (RTLdfs.fn_code f) new_code); 
                        eauto.
                      rewrite Hpred; auto.
                    + boolInv; eapply check_valid_index_phis_correct; eauto.
                    + intros T; rewrite T in *; congruence.                   

                }
                                          

            + {
                constructor 1 with instr; simpl; auto.
                - constructor 1 with instr; simpl; auto.
                - assert (Ni:~ In j jpoints).
                  { intro T; elim (H6 _ T); auto; congruence. }
                  case_eq (phiblock!j); auto; intros phi Hphi1.
                  exploit fold_build_phi_block_correct; eauto.
                  intros [T _].
                  exploit T; eauto; rewrite PTree.gempty.
                  destruct 1; intuition; congruence.
                - (* wt_eidx. *)
                  assert (HG: (entry_Gamma f) ! (RTLdfs.fn_entrypoint f) = Some (PTree.empty index)).
                  unfold entry_Gamma.
                  rewrite PTree.gss; auto.    
                  rewrite (H _ _ HG).
                  replace (read_gamma (PTree.empty index)) with (fun _ : Registers.reg => 1%positive); auto.
                  apply extensionality.
                  intros; unfold read_gamma; simpl; rewrite PTree.gempty; auto.
                - (* wt_instr *)
                  case_eq (G!i); [intros gi Hgi| intuition;fail].
                  case_eq (G!j); [intros gj Hgj| intuition;fail].
                  exploit H2; eauto.
              }
        }

      * assert (Hi:exists instr, new_code!i = Some instr).
        { inv H12; simpl in *; eauto. }
        destruct Hi as [instrs Hi].
        econstructor; eauto.
        exploit H10; eauto; rewrite PTree.gempty; destruct 1; try congruence.
        destruct H13 as [G1 [G2 G3]].
        case_eq (G!i); [intros gi Hgi| intuition;fail].
        exploit H4; eauto.
        exploit H9; eauto; rewrite PTree.gempty; destruct 1; auto; congruence.
        inv H12 ; simpl in H13; rewrite Hi in H13 ; inv H13; econstructor; eauto.

    + (** wf_init **)
      assert (HG: (entry_Gamma f) ! (RTLdfs.fn_entrypoint f) = Some (PTree.empty index)).
      { unfold entry_Gamma.
        rewrite PTree.gss; auto.
      }
      split.
      {
        constructor; simpl; intros.
        split.
        - exploit list_in_map_inv; eauto; simpl; intros [r [Hr1 Hr2]]; subst.
          eapply Bij.from_valid_index_to_valid_reg_ssa; eauto.
        - rewrite (H _ _ HG).
          exploit list_in_map_inv; eauto; simpl; intros [r [Hr1 Hr2]]; subst.
          exists r.
          unfold read_gamma; simpl; rewrite PTree.gempty; auto.
          rewrite Bij.BIJ1; auto.
      }

      split.

      { constructor; simpl; auto.
        rewrite map_map_erase. auto. intros.
        auto.
        unfold erase_code; simpl.
        intros ; intuition.
        rewrite PTree.gmap ; eauto.
        case_eq (RTLdfs.fn_code f) ! p; intros.
        exploit HDFS ; eauto. intros.   
        exploit H2 ; eauto.
        intros. rewrite H12 in * ; simpl in *.
        rewrite <- H14 ; unfold get_opt, option_map; reflexivity.
        case_eq (new_code ! p) ; intros.
        exploit H9 ; eauto. intros [HH1 | HH2].
        exploit H2 ; eauto.
        intros. rewrite H13 in * ; simpl in *.
        rewrite H12 in H14 ; unfold get_opt, option_map in *. congruence.
        rewrite PTree.gempty in HH2.  inv HH2. 
        reflexivity.
      }

      split.
      { apply Hcheck. }

      split. split.
      { intros pc pc0 phiinstr args dst k HH10 H12 H13; simpl in *.
        assert (In pc jpoints).
        exploit fold_build_phi_block_correct; eauto; intros [T _].
        eelim T; eauto.
        rewrite PTree.gempty; congruence.
        unfold successors in *; simpl in *.
        exploit fold_build_phi_block_def_phi_some; eauto.
        intros [d [D1 D2]].
        generalize dependent H12.
        unfold index_pred, successors_list in *.
        case_eq ((make_predecessors new_code successors_instr) ! pc); intros.  
        replace (make_predecessors new_code successors_instr)
          with (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) in *.
        exploit fold_build_phi_block_value; eauto.
        intros.
        inv H16.
        assert (nth_okp k l).
        { eapply get_index_acc_nth_okp; eauto. }
        rewrite HH10 in H18; inv H18.
        
        generalize (In_Iphi_fold2 _ _ _ _ _ _ _ H13); eauto.

        - (* *) 
          erewrite same_successors_same_predecessors; eauto.
          eapply aux_same_succ; eauto.
        - inv H15. 
      }
      
      { intros pc block; simpl; intros.
        assert (In pc jpoints).
        exploit fold_build_phi_block_correct; eauto; intros [T _].
        eelim T; eauto.
        rewrite PTree.gempty; congruence.
        exploit fold_build_phi_block_def_phi_some; eauto.
        intros [d [D1 _]].
        exploit H6; eauto; destruct 1 as [V|V]; [elim V|idtac].
        case_eq ((make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr)!pc); [intros l|idtac];
          intros Hl; unfold is_joinpoint in *; rewrite Hl in *; try congruence; clear V.
        exploit fold_build_phi_block_value; eauto.
        intros F; inv F.  
        rewrite H19 in H12; inv H12.
        assert (forall x, In x (PTree.elements d) -> Bij.valid_index size (snd x) = true).
        { intros.
          boolInv; eapply check_valid_index_phis_correct; eauto.
          eapply PTree.elements_complete; eauto.
          rewrite <- surjective_pairing; eauto.
        }
        eapply In_Iphi_fold7 with (2:= H14) (3:= H15); eauto.
      }

      split. 
      { unfold check_code_at_phipoints in Hcap; simpl in Hcap.
        intros; exploit forall_ptree_true; eauto.
        simpl.
        destruct (new_code!pc); simpl; eauto; congruence.
      }

      (* make_predecessors *)
      assert (TT: ∀pc : RTL.node, RTLutils.join_point pc f ↔ join_point pc {|
                                                        fn_sig := RTLdfs.fn_sig f;
                                                        fn_params := map (fun r : Registers.reg => Bij.pamr size (r, dft_pos))
                                                                         (RTLdfs.fn_params f);
                                                        fn_stacksize := RTLdfs.fn_stacksize f;
                                                        fn_code := new_code;
                                                        fn_phicode := phiblock;
                                                        fn_entrypoint := RTLdfs.fn_entrypoint f;
                                                        fn_ext_params := ext_params_list new_code phiblock
                             (map (λ r : Registers.reg, Bij.pamr size (r, dft_pos)) (RTLdfs.fn_params f));
                                                        fn_dom_test := domtest |}).
      { intros pc. 
        rewrite is_joinpoint_iff_join_point ; eauto.
        rewrite is_joinpoint_iff_join_point_ssa ; eauto.  
        unfold successors, successors.  simpl.
        replace (make_predecessors new_code successors_instr)
          with (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) in *. intuition. 
        erewrite same_successors_same_predecessors; eauto.
        eapply aux_same_succ; eauto.
      }  

      split.
      { apply TT. }

      split. 
      { intros.
        exploit fold_build_phi_block_correct ; eauto.
        intros [HH _]. exploit HH ; eauto.
        intros [HH1 | HH2]. exploit H6 ; eauto.
        intros [HH1' | HH2']. inv HH1'.
        rewrite <- TT.
        rewrite is_joinpoint_iff_join_point; auto.
        rewrite PTree.gempty in HH2. inv HH2.
      }

      split.
      { intros.
        assert (In jp jpoints).
        exploit fold_build_phi_block_correct; eauto; intros [T _].
        eelim T; eauto.
        rewrite PTree.gempty; congruence.
        exploit H6; eauto.
        destruct 1 as [V1|V1].
        elim V1.
        unfold successors in *; simpl in *.
        exploit fold_build_phi_block_def_phi_some; eauto.
        intros [d [D1 D2]].
        generalize dependent H12.
        unfold index_pred, successors_list in *.
        case_eq ((make_predecessors new_code successors_instr) !jp); intros.  
        replace (make_predecessors new_code successors_instr)
          with (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) in *.
        exploit fold_build_phi_block_value; eauto.
        intros.
        inv H16.
        rewrite H15 in H18; inv H18.
        generalize (In_Iphi_fold1' _ _ _ _ _ _ _ H13); eauto.
        (* *) 
        erewrite same_successors_same_predecessors; eauto.
        eapply aux_same_succ; eauto.
        rewrite <- is_joinpoint_iff_join_point in V1.
        rewrite TT in V1.
        rewrite is_joinpoint_iff_join_point_ssa in V1.
        generalize V1; unfold successors, is_joinpoint.   simpl.
        rewrite H12; congruence.
      }

      split.
      { intros.
        assert (In jp jpoints).
        exploit fold_build_phi_block_correct; eauto; intros [T _].
        eelim T; eauto.
        rewrite PTree.gempty; congruence.
        exploit H6; eauto.
        destruct 1 as [V1|V1].
        elim V1.
        rewrite <- TT.
        rewrite is_joinpoint_iff_join_point; auto.
      }

      split.
      { intros.
        assert (In jp (fn_dfs f)).
        exploit H9; eauto.
        rewrite PTree.gempty; destruct 1; auto; congruence.
        exploit fold_build_phi_block_correct; eauto; intros [_ [T _]].
        apply T.
        exploit H10; eauto; destruct 1.
        rewrite PTree.gempty in *; congruence.
        destruct H15 as [H15 _].
        case_eq (G!jp); intros; try congruence.
        eapply H11; eauto.
        rewrite <- is_joinpoint_iff_join_point; auto.
        rewrite TT; auto.
      }

      { intros i.
        case_eq ((RTLdfs.fn_code f)!i); intros.
        exploit HDFS; eauto; intros Hi.
        exploit H2; eauto.
        rewrite H12; auto.
        case_eq (new_code!i); intros.
        exploit H9; eauto; destruct 1.
        exploit H2; eauto.
        congruence.
        rewrite PTree.gempty in *; congruence.
        reflexivity.
      }
Qed. 

(** Smaller lemmas, derived from the main lemma. These are to be used
in the proofs.*)

Lemma typecheck_function_correct_sig:
  forall size f tf def def_phi live ,
    typecheck_function f size def def_phi live = OK tf ->
    RTLdfs.fn_sig f = fn_sig tf.
Proof.
  intros.
  unfold typecheck_function in H.
  destruct Bij.valid_index; try congruence.
  destruct andb; try congruence.
  destruct check_function_inv; try congruence.
  destruct (fold_left
          (update_ctx size (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) def
             def_phi (RTLdfs.fn_code f) live) (fn_dfs f)
          (OK (entry_Gamma f, PTree.empty instruction, nil))); try congruence.
  destruct p ; destruct p.
  monadInv H.
  destruct (compute_test_dom (RTLdfs.fn_entrypoint f) t0) ; try congruence.
  case_eq (check_unique_def {|
              fn_sig := RTLdfs.fn_sig f;
              fn_params := map (fun r : Registers.reg => Bij.pamr size (r, dft_pos))
                             (RTLdfs.fn_params f);
              fn_stacksize := RTLdfs.fn_stacksize f;
              fn_code := t0;
              fn_phicode := x;
              fn_entrypoint := RTLdfs.fn_entrypoint f;
             fn_ext_params := ext_params_list t0 x
                                (map (λ r : Registers.reg, Bij.pamr size (r, dft_pos))
                                   (RTLdfs.fn_params f));
             fn_dom_test := b |}); intros Hif ; rewrite Hif in *.
  destruct check_code_at_phipoints; simpl in EQ0; try congruence.
  inversion EQ0. auto.
  simpl in *; congruence.  
Qed.

Lemma typecheck_function_correct_ssize:
  forall size f tf def def_phi live ,
    typecheck_function f size def def_phi live = OK tf ->
    RTLdfs.fn_stacksize f = fn_stacksize tf.
Proof.
  intros.
  unfold typecheck_function in H.
  destruct Bij.valid_index; try congruence.
  destruct andb; try congruence.
  case_eq (check_function_inv f (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr)) ; intros Hif ; rewrite Hif in *; try congruence.
  destruct (fold_left 
          (update_ctx size (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) def
             def_phi (RTLdfs.fn_code f) live) (fn_dfs f)
          (OK (entry_Gamma f, PTree.empty instruction, nil))); try congruence.
  destruct p ; destruct p.
  monadInv H.
  destruct (compute_test_dom (RTLdfs.fn_entrypoint f) t0) ; try congruence.
  case_eq (check_unique_def {|
              fn_sig := RTLdfs.fn_sig f;
              fn_params := map (fun r : Registers.reg => Bij.pamr size (r, dft_pos))
                             (RTLdfs.fn_params f);
              fn_stacksize := RTLdfs.fn_stacksize f;
              fn_code := t0;
              fn_phicode := x;
              fn_entrypoint := RTLdfs.fn_entrypoint f;
            fn_ext_params := ext_params_list t0 x
                               (map (λ r : Registers.reg, Bij.pamr size (r, dft_pos)) (RTLdfs.fn_params f));
            fn_dom_test := b|}); intros Hif' ; rewrite Hif' in *.
  destruct check_code_at_phipoints; simpl in EQ0; try congruence.
  inversion EQ0. auto.
  simpl in *; congruence.
Qed.

Lemma typecheck_function_correct_udef:
  forall size f tf def def_phi live ,
    typecheck_function f size def def_phi live = OK tf ->
    unique_def_spec tf.
Proof.
  intros.
  unfold typecheck_function in H.
  destruct Bij.valid_index; try congruence.
  destruct andb; try congruence.
  destruct check_function_inv; try congruence.
  destruct (fold_left
          (update_ctx size (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr) def
             def_phi (RTLdfs.fn_code f) live) (fn_dfs f)
          (OK (entry_Gamma f, PTree.empty instruction, nil))); try congruence.
  destruct p ; destruct p.
  monadInv H.
  destruct (compute_test_dom (RTLdfs.fn_entrypoint f) t0) ; try congruence.
  case_eq (check_unique_def {|
              fn_sig := RTLdfs.fn_sig f;
              fn_params := map (fun r : Registers.reg => Bij.pamr size (r, dft_pos))
                             (RTLdfs.fn_params f);
              fn_stacksize := RTLdfs.fn_stacksize f;
              fn_code := t0;
              fn_phicode := x;
              fn_entrypoint := RTLdfs.fn_entrypoint f;
            fn_ext_params := ext_params_list t0 x
                               (map (λ r : Registers.reg, Bij.pamr size (r, dft_pos)) (RTLdfs.fn_params f));
            fn_dom_test := b|}); intros Hif' ; rewrite Hif' in *.
  destruct check_code_at_phipoints; simpl in *; try congruence.
  inversion EQ0.
  eapply check_unique_def_correct ; eauto.
  simpl in *; congruence.
Qed.

Require Import RTLdfsgen RTLdfsproof.

Lemma typecheck_function_correct_erase:
  forall size f tf def def_phi live,
    RTLdfsgen.wf_dfs_function f  ->
    typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
    check_erased_spec size f tf.
Proof.
  intros size f tf def def_phi live HDFS Hok.
  inv HDFS; exploit typecheck_function_correct; eauto.
  destruct 1; intuition.
Qed.

Lemma typecheck_function_correct_phiparams:
  forall size f tf def def_phi live,
    RTLdfsgen.wf_dfs_function f ->
    typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
    check_phi_params_spec tf.
Proof.
  intros.
  inv H; exploit typecheck_function_correct; eauto.
  destruct 1.
  decompose [and] H; auto.
Qed.

Lemma typecheck_function_correct_noduplicates:
  forall size f tf def def_phi live ,
    RTLdfsgen.wf_dfs_function f ->
    typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
    check_no_duplicates_spec size tf.
Proof.
  intros.
  inv H; exploit typecheck_function_correct; eauto.
  destruct 1.
  decompose [and] H; auto.
Qed.

Lemma typecheck_function_correct_structural_checks:
  forall size f tf def def_phi live ,
    RTLdfsgen.wf_dfs_function f ->
    typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
    structural_checks_spec size f tf.
Proof.
  intros.
  constructor. eapply typecheck_function_correct_sig; eauto.
  constructor. eapply typecheck_function_correct_ssize; eauto.
  constructor. eapply typecheck_function_correct_erase; eauto.
  constructor. eapply typecheck_function_correct_udef; eauto.
  constructor. eapply typecheck_function_correct_phiparams; eauto.
  eapply typecheck_function_correct_noduplicates; eauto.
Qed.

Lemma fn_ssa_params1 : forall size f tf def def_phi live ,
    RTLdfsgen.wf_dfs_function f ->
    typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
    forall x pc, In x (fn_params tf) -> ~ assigned_code_spec (fn_code tf) pc x.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto; [ eapply fn_dfs_comp ; eauto|eapply fn_dfs_norep ; eauto|idtac].
  intros [G [HWT [HWFI [HER HPHI]]]].
  intros Hcont.
  inv HWFI. exploit H2 ; eauto. intros [_ [r Heq]] ; subst.
   (inv Hcont;
    inv HWT; (exploit (WTE pc succ) ; eauto );
    try (econstructor ; eauto ; simpl ; eauto));
  (intros Hwte; inv Hwte; ( inv EIDX; congruence)).
Qed.

Lemma fn_ssa_params2 : forall size f tf def def_phi live ,
  RTLdfsgen.wf_dfs_function f ->
  typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
  forall x pc, In x (fn_params tf) -> ~ assigned_phi_spec (fn_phicode tf) pc x.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto; [ eapply fn_dfs_comp ; eauto|eapply fn_dfs_norep ; eauto|idtac].
  intros [G [HWT [HWFI [HERASE [HNORM [[HPHI HPHI3] [HPHI4 [HJP [HPHI5 HPHI6]]]]]]]]].
  intro Hcont.
  inv HWFI. exploit H2 ; eauto. intros [_ [r Heq]] ; subst.
  inv Hcont. destruct H4.
  exploit HPHI4 ; eauto. intros [ins Hins].
  exploit HPHI5 ; eauto. intros Hjp.
  inv Hjp.
  assert (exists p0, In p0 l). destruct l ; simpl in *. inv Hl. exists p. eauto.
  destruct H5 as [p0 Hin].
  assert ((make_predecessors (fn_code tf) (successors_instr)) !!! pc = l).
  unfold successors_list. rewrite Hpreds ; simpl ; auto.
  exploit @make_predecessors_some; eauto. intros [ip0 Hip0].
  rewrite <- H5 in Hin.
  assert (HH : In pc (successors_instr ip0)).
  eapply @KildallComp.make_predecessors_correct2; eauto.
  
  assert (is_edge tf p0 pc). econstructor ; eauto.
  inv HWT; (exploit (WTE p0 pc) ; eauto ).
  intros Hwte; inv Hwte; allinv.
  inv PEIDX.
  eelim H5 with (ri:= x) ; eauto.
  econstructor; eauto.
Qed.

Lemma fn_reached : forall size f tf def def_phi live ,
  RTLdfsgen.wf_dfs_function f ->
  typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
  forall pc ins, (fn_code tf) ! pc = Some ins -> reached tf pc.
Proof.
  intros.
  assert (∀i : positive, get_opt (erase_instr size) (fn_code tf) ! i = get_opt (fun x => x) (RTLdfs.fn_code f) ! i).
  { exploit typecheck_function_correct ; eauto; [ eapply fn_dfs_comp ; eauto|eapply fn_dfs_norep ; eauto|idtac].
    intros [G HG].
    decompose [and] HG; assumption.
  }
  assert (exists ins', (RTLdfs.fn_code f)!pc = Some ins').
    generalize (H2 pc); rewrite H1; simpl.
    case_eq ((RTLdfs.fn_code f)!pc); simpl; try congruence; eauto.
  destruct H3 as [ins' H3].
  assert (In pc (fn_dfs f)).
    inv H; eauto.
  assert (forall i j, RTLutils.cfg (RTLdfs.fn_code f) i j -> cfg tf i j).
    intros i j T.
    inv T.
    generalize (H2 i); rewrite HCFG_ins; simpl.
    case_eq ((fn_code tf)!i); simpl; try congruence; intros.
    inv H6.
    replace (RTLdfs.successors_instr (erase_instr size i0)) with (successors_instr i0) in *.
    econstructor; eauto.
    destruct i0 ; simpl ; eauto.
    destruct s0 ; simpl ; eauto.
    destruct s0 ; simpl ; eauto.
    destruct o; simpl ; eauto.
  assert (forall i j, (RTLutils.cfg (RTLdfs.fn_code f))** i j -> (cfg tf)** i j).
    induction 1.
    constructor 1; auto.
    constructor 2.
    constructor 3 with y; auto.
  apply H6. 
  replace (fn_entrypoint tf) with (RTLdfs.fn_entrypoint f).
  eapply fn_dfs_reached; eauto.
  
  unfold typecheck_function in H0.
  destruct Bij.valid_index; try congruence.
  destruct andb; try congruence.
  destruct check_function_inv; try (inv H0; fail).
  destruct (fold_left
           (update_ctx size (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr)
              def def_phi (RTLdfs.fn_code f)
              (fun pc : node => Lin f pc (Lout live)))
           (fn_dfs f) (OK (entry_Gamma f, PTree.empty instruction, nil))); try (inv H0; fail).
  destruct p; destruct p.
  destruct (fold_left
            (build_phi_block size
               (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr)
               (fun pc : node => Lin f pc (Lout live)) def_phi t) l
            (OK (PTree.empty phiblock))); try (inv H0; fail).
  simpl in H0.
  destruct compute_test_dom; try (inv H0; fail).
  destruct check_unique_def; try (inv H0; fail).
  destruct check_code_at_phipoints; simpl in H0; inversion H0; clear H0.
  simpl; auto.
Qed.

Lemma fn_entry : forall size f tf def def_phi live ,
  RTLdfsgen.wf_dfs_function f ->
  typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
  exists s, (fn_code tf) ! (fn_entrypoint tf) = Some (Inop s).
Proof.
  intros.
  exploit typecheck_function_correct ; eauto; [ eapply fn_dfs_comp ; eauto|eapply fn_dfs_norep ; eauto|idtac].
  intros [G [HWT [HWFI [HER [H' HPHI]]]]]. inv HER.
  inv H'. unfold check_function_inv in H2.
  case_eq (RTLdfs.fn_code f) ! (RTLdfs.fn_entrypoint f) ; intros.
  rewrite H1 in * ; destruct i ; try congruence.
  rewrite HCODE in H1.
  unfold erase_code in H1. rewrite PTree.gmap in H1.
  unfold option_map in H1.
  rewrite HENTRY in *.
  destruct ((fn_code tf) ! (fn_entrypoint tf)); try congruence.
  destruct i; simpl in *; try congruence.
  eauto.
  destruct s0; try congruence.
  destruct s0; try congruence.
  destruct o; try congruence.
  rewrite H1 in * ; congruence.
Qed.

Lemma fn_phicode_code : forall size f tf def def_phi live ,
  RTLdfsgen.wf_dfs_function f ->
  typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
  forall pc block,
    (fn_phicode tf) ! pc = Some block ->
    exists ins, (fn_code tf) ! pc = Some ins.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto;
    [ eapply fn_dfs_comp ; eauto|
      eapply fn_dfs_norep ; eauto|
      idtac].
  intros [G HH]. decompose [and] HH.
  eauto.
Qed.

Lemma fn_code_closed:forall size f tf def def_phi live ,
  RTLdfsgen.wf_dfs_function f ->
  typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
  forall pc pc' instr, tf.(fn_code) ! pc = Some instr ->
    In pc' (successors_instr instr) ->
    exists instr', tf.(fn_code) ! pc' = Some instr'.
Proof.
  intros.
  exploit typecheck_function_correct_erase ; eauto. intros Herased; inv Herased.
  unfold typecheck_function in H0.
  destruct Bij.valid_index; try congruence.
  destruct andb; try congruence.
  case_eq (check_function_inv f (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr)) ; intros Hif ; rewrite Hif in *.
  assert ((erase_code size tf) ! pc = Some (erase_instr size instr)).
  unfold erase_code ; rewrite PTree.gmap ; unfold option_map ; rewrite H1.
  auto.
  rewrite <- HCODE in H3.
  exploit (check_function_inv_correct0 f Hif pc pc') ; eauto.
  assert ((successors_instr instr) = (RTL.successors_instr (erase_instr size instr))).
  induction instr ; simpl ; eauto.
  destruct s0 ; simpl ; eauto.
  destruct s0 ; simpl ; eauto.
  destruct o; simpl ; eauto.
  rewrite H4 in *. auto.
  intros [instr' Hinstr'].
  rewrite HCODE in Hinstr'.
  unfold erase_code in Hinstr' ; rewrite PTree.gmap in Hinstr' ; unfold option_map in *.
  destruct (fn_code tf) ! pc'. exists i ; auto.
  congruence.
  congruence.
Qed.

Lemma fn_entrypoint_inv: forall size f tf def def_phi live ,
  RTLdfsgen.wf_dfs_function f ->
  typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
  (exists i, (tf.(fn_code) ! (tf.(fn_entrypoint)) = Some i)) /\
  ~ join_point tf.(fn_entrypoint) tf.
Proof.
intros.
  exploit typecheck_function_correct_erase ; eauto. intros Herased; inv Herased.
  exploit typecheck_function_correct ; eauto.
  eapply fn_dfs_comp ; eauto.
  eapply fn_dfs_norep ; eauto.
  intros [_ [_ [_ [_ [_ [_ [_ [HH _]]]]]]]].
  
  unfold typecheck_function in H0.
  destruct Bij.valid_index ; try congruence.
  destruct andb; try congruence.
  case_eq (check_function_inv f (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr)) ; intros Hif ; rewrite Hif in *.
  assert (exists ins, (RTLdfs.fn_code f) ! (RTLdfs.fn_entrypoint f) = Some ins).
  eapply (check_function_inv_correct11 f) ; eauto.
  split.
  destruct H1. rewrite HCODE in H1. unfold erase_code in H1. rewrite PTree.gmap in H1.
  unfold option_map in H1. rewrite HENTRY in H1.
  destruct (fn_code tf) ! (fn_entrypoint tf); intros. exists i ; auto. congruence.
  eapply (check_function_inv_correct12 f) in Hif ; eauto.
  clear H0.
  intro Hcont. rewrite HENTRY in * . eelim (HH (fn_entrypoint tf)) ; eauto.
  congruence.
Qed.

Lemma fn_code_inv2: forall size f tf def def_phi live ,
  RTLdfsgen.wf_dfs_function f ->
  typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
  forall jp pc i, (join_point jp tf) ->
    In jp ((successors tf) !!! pc) ->
    tf.(fn_code) ! jp = Some i ->
    tf.(fn_code) ! pc = Some (Inop jp).
Proof.
  intros.
  exploit typecheck_function_correct ; eauto; [ eapply fn_dfs_comp ; eauto|eapply fn_dfs_norep ; eauto|idtac].
  intros [G [HWT [HWFI [HERASE [HNORM [[HPHI HPHI3] [HPHI4 [HJP HPHI5]]]]]]]].
  inv HNORM. inv HERASE.
  assert ((RTLdfs.fn_code f) ! jp = Some (erase_instr size i)).
  rewrite HCODE. unfold erase_code ; rewrite PTree.gmap ; unfold option_map.
  rewrite H3 ; auto.
  assert (In jp (RTLdfs.successors_map f) !!! pc).
  unfold successors_list, RTLdfs.successors_map. rewrite PTree.gmap1.
  unfold option_map.
  unfold successors, successors_list in H2.
  rewrite PTree.gmap1 in H2. unfold option_map in H2.
  case_eq (fn_code tf) ! pc ; intros; rewrite H6 in *; [| inv H2].
  assert ((RTLdfs.fn_code f) ! pc = Some (erase_instr size i0)).
  rewrite HCODE. unfold erase_code ; rewrite PTree.gmap ; unfold option_map.
  rewrite H6 ; auto.
  rewrite H7. destruct i0 ; simpl ; eauto.
  destruct s0 ; simpl ; eauto.
  destruct s0 ; simpl ; eauto.
  destruct o ; simpl ; eauto.
  exploit check_function_inv_correct3 ; eauto.
  eapply HJP; auto.
  intros.
  rewrite HCODE in H7. unfold erase_code in H7.
  rewrite PTree.gmap in H7. unfold option_map in H7.
  destruct ((fn_code tf) ! pc) ; [destruct i0 ; simpl in * ; try congruence|].
  destruct s0 ; simpl ; congruence.
  destruct s0 ; simpl ; congruence.
  destruct o ; simpl ; congruence. congruence.
Qed.
  

Lemma fn_phicode_inv1: forall size f tf def def_phi live ,
  RTLdfsgen.wf_dfs_function f ->
  typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
  forall phib jp i,
    tf.(fn_code) ! jp = Some i ->
    tf.(fn_phicode) ! jp = Some phib ->
    join_point jp tf.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto; [ eapply fn_dfs_comp ; eauto|eapply fn_dfs_norep ; eauto|idtac].
  intros [G HH]; decompose [and] HH.
  eauto.
Qed.

Lemma fn_phicode_inv2: forall size f tf def def_phi live ,
  RTLdfsgen.wf_dfs_function f ->
  typecheck_function f size def def_phi (fun pc => (Lin f pc (Lout live))) = OK tf ->
  forall jp i,
    join_point jp tf ->
    tf.(fn_code) ! jp = Some i ->
    exists phib, tf.(fn_phicode) ! jp = Some phib.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto; [ eapply fn_dfs_comp ; eauto|eapply fn_dfs_norep ; eauto|idtac].
  intros [G HH]; decompose [and] HH.
  eauto.
Qed.

Lemma typecheck_function_fn_uacf : forall size f def def_phi tf live,
  RTLdfsgen.wf_dfs_function f ->
  (wf_live f (Lout live)) ->
  typecheck_function f size def def_phi (fun pc0 : node => Lin f pc0 (Lout live)) = OK tf ->
  ∀x : reg,
  ∀pc : node,
  use_code tf x pc
  → assigned_code_spec (fn_code tf) pc x → False.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto.
  eapply fn_dfs_comp ; eauto.
  eapply fn_dfs_norep ; eauto.
  intros [G [HWT [HWFI [HER HPHI]]]]. inv HER.
  exploit wt_def_use_code_false; eauto. constructor ; eauto.

  eapply typecheck_function_correct_udef ; eauto.
  
  eapply fn_ssa_params1 ; eauto.
  eapply fn_ssa_params2 ; eauto.
  eapply fn_reached ; eauto.
  eapply fn_entry ; eauto.
  eapply fn_phicode_code ; eauto.
  eapply fn_code_closed ; eauto.
  eapply fn_entrypoint_inv ; eauto.
  eapply fn_code_inv2 ; eauto.
  eapply fn_phicode_inv1 ; eauto.
Qed.

Lemma typecheck_function_fn_strict : forall size f def def_phi tf live,
  RTLdfsgen.wf_dfs_function f ->
  (wf_live f (Lout live)) ->
  typecheck_function f size def def_phi (fun pc0 : node => Lin f pc0 (Lout live)) = OK tf ->
   ∀x : reg, ∀u d : node, use tf x u → SSA.def tf x d → dom tf d u.
Proof.
  intros.
  exploit typecheck_function_correct ; eauto.
  eapply fn_dfs_comp ; eauto.
  eapply fn_dfs_norep ; eauto.
  intros [G [HWT [HWFI [HER HPHI]]]]. inv HER.
  exploit wt_pdom; eauto. constructor ; eauto.
  eapply typecheck_function_correct_udef ; eauto.
  eapply fn_ssa_params1 ; eauto.
  eapply fn_ssa_params2 ; eauto.
  eapply fn_reached ; eauto.
  eapply fn_entry ; eauto.
  eapply fn_phicode_code ; eauto.
  eapply fn_code_closed ; eauto.
  eapply fn_entrypoint_inv ; eauto.
  eapply fn_code_inv2 ; eauto.
  eapply fn_phicode_inv1 ; eauto.
Qed.

(** * Correctness of dominator test *)
Require Import DLib.
Import SSADomTest.

Lemma check_D_eq_correct : forall f sn itvm,
  let l := extern_d (fn_entrypoint f) (fn_code f) in 
  let D := SSADomTest.make_D_fun l in 
   SSADomTest.build_succs (fn_entrypoint f) l = Some sn -> 
   SSADomTest.build_itv_map (fn_entrypoint f) sn = Some itvm ->
   check_D_eq (fn_entrypoint f) (fn_code f) D (fun i j => SSADomTest.is_ancestor itvm (D j) i) = true -> 
   SSADomTest.D_spec (fn_entrypoint f) (SSA.cfg f) D.
Proof.
  unfold check_D_eq.
  intros.
  eapply andb_prop in H1; eauto. intuition.
  split.
  - destruct peq; simpl in * ; congruence.
  - intros. invh cfg.
    set (fpt :=
           (fun pc succ_pc => forallb
                                (fun j => is_ancestor itvm0
                                                      (make_D_fun (extern_d (fn_entrypoint f) (fn_code f)) j)
                                                      pc)
                                succ_pc)) in *.    
    assert (Hi : fpt i (successors_instr ins) = true).
    { eapply forall_ptree_true; eauto.
      unfold successors.
      rewrite PTree.gmap1, HCFG_ins; auto. 
    }
  unfold fpt in *. eapply forallb_forall in Hi; eauto.
  eapply is_ancestor_spec with (1:= (cfg f)) (2:= exit f); eauto. 
Qed.
  
Theorem dom_test_correct : forall f test_dom, 
                             compute_test_dom (fn_entrypoint f) (fn_code f) = Some test_dom ->
                             forall i j,
                               reached f j ->
                               test_dom i j = true -> 
                               dom f i j.
Proof.
  intros. 
  unfold compute_test_dom in *; flatten H; subst; try congruence.
  unfold dom.
  eapply D_spec_correct; eauto.
  - eapply check_D_eq_correct; eauto. 
  - eapply is_ancestor_spec with (1:= (cfg f)) (2:= exit f); eauto.
Qed.

(** * All generated function satisfy [wf_ssa_function] *)
Lemma typecheck_function_wf_ssa_function : forall f size def def_phi tf live,
  RTLdfsgen.wf_dfs_function f ->
  (wf_live f (Lout live)) ->
  typecheck_function f size def def_phi (fun pc0 : node => Lin f pc0 (Lout live)) = OK tf ->
  wf_ssa_function tf.
Proof.
  intros.
  constructor.
  
  - eapply typecheck_function_correct_udef ; eauto.
  - split; intros.
    eapply fn_ssa_params1 ; eauto.
    eapply fn_ssa_params2 ; eauto.
  - eapply typecheck_function_fn_strict ; eauto.
  - eapply typecheck_function_fn_uacf ; eauto.
  - exploit typecheck_function_correct ; eauto.
    eapply fn_dfs_comp ; eauto.
    eapply fn_dfs_norep ; eauto.
    intros [G HG]; decompose [and] HG.
    intros pc phib args x T1 T2.
    symmetry; eapply H11; eauto.

  - intros.
    case_eq ((fn_code tf) ! jp) ; intros.
    eapply fn_code_inv2 ; eauto.
    unfold successors_list, successors in H3.
    rewrite PTree.gmap1 in H3.
    case_eq ((fn_code tf) ! pc) ; intros; rewrite H5 in *; simpl in *.
    exploit fn_code_closed ; eauto. intros. destruct H6.
    congruence.
    intuition.

  - intros.
    split; intros.
    intro Hcont.
    inv H2.
    assert (exists p, In p l).
    destruct l. simpl in * . lia. eauto. destruct H2.
    assert ((make_predecessors (fn_code tf) successors_instr) !!! jp = l).
    unfold successors_list ; rewrite Hpreds ; simpl ; auto.
    exploit @make_predecessors_some; eauto. intros [ix Hix].
    assert (HH : In jp (successors_instr ix)).
    eapply @KildallComp.make_predecessors_correct2 ; eauto.
    unfold successors_list, successors in *.
    rewrite Hpreds in *.
    unfold make_preds. rewrite Hpreds in *. auto.
    exploit fn_code_closed ; eauto. intros [ins' Hins'].
    exploit fn_phicode_inv2 ; eauto.
    econstructor; eauto. intros.
    destruct H4. congruence.
    case_eq (fn_phicode tf) ! jp ; intros; [| congruence].
    exploit fn_phicode_code ; eauto. intros [ins Hins].
    exploit fn_phicode_inv1 ; eauto.
   
  - eapply fn_reached ; eauto.
  - eapply fn_code_closed ; eauto.
  - eapply fn_entry ; eauto.
  
  - exploit typecheck_function_correct_erase ; eauto. intros Herased.
    unfold typecheck_function in H1.
    destruct Bij.valid_index; try congruence.
    destruct andb; try congruence.
    case_eq (check_function_inv f (make_predecessors (RTLdfs.fn_code f) RTLdfs.successors_instr)) ;
      intros Hif ; rewrite Hif in *.
    clear H1. intros.
    intro Hcont. inv Hcont.
    inv Herased.
    assert ((RTLdfs.fn_code f) ! pc = (Some (erase_instr size ins))).
    rewrite HCODE.
    unfold erase_code. rewrite PTree.gmap. unfold option_map. rewrite HCFG_ins. auto.
    eelim (check_function_inv_correct01 f Hif pc) ; eauto.
    rewrite HENTRY.
    destruct ins ; simpl ; eauto.
    destruct s0 ; simpl ; eauto.
    destruct s0 ; simpl ; eauto.
    destruct o ; simpl ; eauto.
    congruence.

  - unfold typecheck_function in *.
    destruct Bij.valid_index; try congruence.
    destruct andb; try congruence.
    destruct check_function_inv; try congruence.
    destruct fold_left ; try congruence.
    destruct p ; destruct p.
    monadInv H1.
    destruct compute_test_dom; try congruence.
    destruct check_unique_def, check_code_at_phipoints; simpl in * ; try congruence.
    inv EQ0; simpl in *.
    eapply ext_params_list_spec; eauto.

  - unfold typecheck_function in *.
    destruct Bij.valid_index; try congruence.
    destruct andb; try congruence.
    destruct check_function_inv; try congruence.
    destruct fold_left ; try congruence.
    destruct p ; destruct p.
    monadInv H1.
    case_eq (compute_test_dom (RTLdfs.fn_entrypoint f) t0); [intros domTest HHeq | intros HHeq];
    try rewrite HHeq in EQ0; try congruence.
    destruct check_unique_def, check_code_at_phipoints; simpl in * ; try congruence.
    inv EQ0; simpl in *.
    intros; eapply dom_test_correct; eauto.
Qed.

Lemma transf_function_wf_ssa_function : forall f tf,
  RTLdfsgen.wf_dfs_function f ->
  SSAvalid.transf_function f = OK tf -> wf_ssa_function tf.
Proof.
  intros.
  unfold transf_function in H0. monadInv H0.
  destruct (extern_gen_ssa f) as [[max def] def_phi].
  eapply typecheck_function_wf_ssa_function ; eauto.
  case_eq (analyze f); intros; rewrite H0 in * ; simpl in *.
  inv EQ. eapply live_wf_live ; eauto.
 congruence.
Qed.
