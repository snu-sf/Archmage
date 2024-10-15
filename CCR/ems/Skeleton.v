Require Import CoqlibCCR.
Require Export ZArith.
Require Import AList.
Require Import String.
Require Import Orders.

Set Implicit Arguments.

Local Open Scope nat_scope.



(* one instance per lang *)
Module Sk.

  Class ld: Type := mk {
    t:> Type;
    unit: t;
    add: t -> t -> t;
    canon: t -> t;
    wf: t -> Prop;
    wf_dec: forall a, {wf a} + {~ wf a} ;
    le: t -> t -> Prop;
    le_PreOrder:> PreOrder le;
    le_canon: forall a, le a (canon a);
    le_canon_rev: forall a, le (canon a) a;
    add_comm: forall a b (WF: wf (add a b)),
        canon (add a b) = canon (add b a);
    add_assoc: forall a b c, add a (add b c) = add (add a b) c;
    add_unit_l: forall a, add unit a = a;
    add_unit_r: forall a, add a unit = a;
    le_add_l: forall a b, le a (add b a);
    le_add_r: forall a b, le a (add a b);
    le_add_both: forall a b c, le a b -> le (add c a) (add c b);
    wf_comm: forall a b, wf (add a b) -> wf (add b a);
    wf_canon: forall a, wf a -> wf (canon a);
    unit_wf: wf unit;
    wf_mon: forall a b, wf (canon (add a b)) -> wf (canon a);
    (* extends := fun a b => exists ctx, canon (add a ctx) = b; *)
  }
  .

End Sk.

Notation gname := string (only parsing). (*** convention: not capitalized ***)
Notation mname := string (only parsing). (*** convention: capitalized ***)

(* auxilary structure to interpret sk as initial global env *)
Module SkEnv.
  Notation mblock := nat (only parsing).
  Notation ptrofs := Z (only parsing).

  Record t: Type := mk {
    blk2id: mblock -> option gname;
    id2blk: gname -> option mblock;
  }
  .

  Definition wf (ske: t): Prop :=
    forall id blk, ske.(id2blk) id = Some blk <-> ske.(blk2id) blk = Some id.
End SkEnv.
