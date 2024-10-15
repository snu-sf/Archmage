Require Export ZArith.
Require Export List.
Require Export Lia.
Require Export Coq.Program.Equality. (**r Necessary for 'dependent induction'. *)

Ltac autoinjection :=
  repeat match goal with
           | h: ?f _ = ?f _ |- _ => injection h; intros; clear h; subst
           | h: ?f _ _ = ?f _  _ |- _ => injection h; intros; clear h; subst
           | h: ?f _ _ _ = ?f _ _ _ |- _ => injection h; intros; clear h; subst
           | h: ?f _ _ _ _ = ?f _ _ _ _ |- _ => injection h; intros; clear h; subst
           | h: ?f _ _ _ _ _ = ?f _ |- _ _ _ _ _ => injection h; intros; clear h; subst
         end.

Ltac go :=
  simpl in *;
  repeat match goal with
         | h: ?x = _ |- context[match ?x with _ => _ end] => rewrite h
         end ;
  autoinjection ;
  try (congruence);
  try lia;
  subst;
  eauto 4 with zarith datatypes;
  try (once (econstructor; solve[go])).

Tactic Notation "go" := try (go; fail).

Ltac inv H := inversion H; try subst; clear H.

(* inv by name of the Inductive relation *)
Ltac invh f :=
    match goal with
      [ id: f |- _ ] => inv id
    | [ id: f _ |- _ ] => inv id
    | [ id: f _ _ |- _ ] => inv id
    | [ id: f _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    | [ id: f _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => inv id
    end.

Tactic Notation "flatten" ident(H) :=
  repeat match goal with
    | H: context[match ?x with | left _ => _ | right _ => _ end] |- _ => destruct x
    | H: context[match ?x with | _ => _ end] |- _ => let E := fresh "Eq" in destruct x eqn:E
  end; autoinjection; try congruence.

Tactic Notation "flatten" :=
  repeat match goal with
    | |- context[match ?x with | left _ => _ | right _ => _ end] => destruct x
    | |- context[match ?x with | _ => _ end] => let E := fresh "Eq" in destruct x eqn:E
  end; autoinjection; try congruence.

Tactic Notation "induction" ident(x) := dependent induction x.

