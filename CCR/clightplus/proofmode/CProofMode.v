Require Import AList.
Require Import ModSem.
Require Export IPM HSim IProofMode.
Require Import ClightPlusMem1.
Require Import ClightPlusgen.
From compcert Require Import Ctypes Clightdefs.

Global Opaque equiv_prov.
Global Opaque has_offset.
Global Opaque points_to.
Global Opaque ccallU.
Global Opaque build_composite_env'.
Global Opaque build_composite_env.

Global Arguments alist_add /.
Global Arguments ClightPlusgen._sassign_c /.
Global Arguments ClightPlusgen._scall_c /.
Global Arguments ClightPlusgen._site_c /.
Global Arguments ClightPlusExprgen.sem_xor_c /.
Global Arguments ClightPlusExprgen.sem_binarith_c /.
Global Arguments ClightPlusExprgen.sem_cast_c /.

Ltac init_hide :=
    repeat (match goal with
    | [ |- context[hide ?p]] =>
        let H := fresh "HIDDEN" in set (H := hide p) at 1
    end).

Ltac unhide H :=
    unfold H in *;
    unfold hide at 1;
    init_hide;
    clear H.

Tactic Notation "unhide" constr(H) :=
  unhide H.

Tactic Notation "unhide" :=
    repeat (match goal with
            | |- context[ITree.bind (?H _ _) _] => unhide H
            | |- context[{| _observe := TauF (ITree.bind (?H _ _) _) |}] => unhide H
            end).

Ltac remove_tau :=
    repeat (ss; hred_r; iApply isim_tau_tgt; ss; hred_r).

Lemma unfold_build_composite_env: forall x,
  build_composite_env x =
  add_composite_definitions (Maps.PTree.empty composite) x.
Proof.
  reflexivity.
Qed.

Ltac alist_composites ce cel :=
  match cel with
  | (?name, Build_composite ?su ?mem ?attr ?size ?align ?rank _ _ _) :: ?tl =>
    pose (s_size := size);
    vm_compute in s_size;
    let s_align := fresh in
    pose (s_align := align);
    vm_compute in s_align;
    let Hco := fresh in
    (assert (Hco: exists co, alist_find name ce = Some co /\
    co_su co = su /\ co_members co = mem /\ co_attr co = attr /\
    co_sizeof co = s_size /\ co_alignof co = s_align /\ co_rank co = rank)
    by now subst ce; ss; eexists; repeat (split; try reflexivity));
    let co := fresh "co" in
    let get_co := fresh "get_co" in
    let co_co_su := fresh "co_co_su" in
    let co_co_members := fresh "co_co_members" in
    let co_co_attr := fresh "co_co_attr" in
    let co_co_sizeof := fresh "co_co_sizeof" in
    let co_co_alignof := fresh "co_co_alignof" in
    let co_co_rank := fresh "co_co_rank" in
    destruct Hco as [co [get_co
      [co_co_su [co_co_members [co_co_attr [co_co_sizeof
      [co_co_alignof co_co_rank]]]]]]];
    unfold s_size in co_co_sizeof;
    unfold s_align in co_co_alignof;
    clear s_size;
    clear s_align;
    match tl with
    | [] => idtac
    | _ => alist_composites ce tl
    end
  end.

Ltac get_composite ce e :=
  let comp_env := fresh in
  match goal with
  | e: build_composite_env ?composites = Errors.OK _ |- _ =>
    pose (comp_env := unfold_build_composite_env composites);
    rewrite e in comp_env; ss
  end;
  let comp_env' := fresh in
  inversion comp_env as [comp_env']; clarify;
  ss; clear e; clear comp_env; unfold Maps.PTree.elements in ce; ss;
  match goal with
  | ce := ?cel |- _ => alist_composites ce cel
  end; clearbody ce;
  repeat match goal with
         | H : alist_find _ ce = Some _ |- _ => unfold Maps.PTree.prev in H
         end; ss.