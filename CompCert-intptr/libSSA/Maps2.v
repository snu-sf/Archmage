Require Import Coqlib.
Require Import Maps.

Set Implicit Arguments.

Module  MakeProdMap (M1:MAP) (M2:MAP) <: MAP.

  Definition elt: Type := (M1.elt * M2.elt)%type.

  Lemma elt_eq: forall (a b: elt), {a = b} + {a <> b}.
  Proof.
    decide equality.
    apply M2.elt_eq.
    apply M1.elt_eq.
  Qed.

  Definition t (A:Type) : Type := M1.t (M2.t A).

  Definition init (A: Type) (a: A) : t A := M1.init (M2.init a).

  Definition get (A: Type) (x:elt) (m:t A) : A :=
    let (x1,x2) := x in
      M2.get x2 (M1.get x1 m).

  Definition set (A: Type) (x:elt) (v:A) (m:t A) : t A :=
    let (x1,x2) := x in
      M1.set x1 (M2.set x2 v (M1.get x1 m)) m.

  Lemma gi:
    forall (A: Type) (i: elt) (x: A), get i (init x) = x.
  Proof.
    intros A [i1 i2] x; unfold get, init.
    rewrite M1.gi.
    rewrite M2.gi; auto.
  Qed.

  Lemma gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), get i (set i x m) = x.
  Proof.
    intros A [i1 i2] x m; unfold get, set.
    rewrite M1.gss; rewrite M2.gss; auto.
  Qed.

  Lemma gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> get i (set j x m) = get i m.
  Proof.
    intros A [i1 i2] [j1 j2] x m H; unfold get, set.
    destruct (M1.elt_eq i1 j1); subst.
    rewrite M1.gss; rewrite M2.gso; congruence.
    rewrite M1.gso; auto.
  Qed.

  Lemma gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get i (set j x m) = if elt_eq i j then x else get i m.
  Proof.
    intros A i j x m.
    destruct (elt_eq i j); subst.
    apply gss.
    apply gso; auto.
  Qed.

  Lemma gsident:
    forall (A: Type) (i j: elt) (m: t A), get j (set i (get i m) m) = get j m.
  Proof.
    intros A i j m.
    destruct (elt_eq i j); subst.
    rewrite gss; auto.
    rewrite gso; auto.
  Qed.

  Definition map (A B: Type) (f: A -> B) (m: t A) : t B :=
    M1.map (M2.map f) m.

  Lemma gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
    get i (map f m) = f(get i m).
  Proof.
    intros A B f [i1 i2] m; unfold get, map.
    rewrite M1.gmap; rewrite M2.gmap; auto.
  Qed.

End MakeProdMap.
