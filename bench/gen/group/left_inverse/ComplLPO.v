(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Parameter e : G.
Parameter f : G -> G -> G.
Parameter i : G -> G.
Axiom associativity : forall X Y Z : G, (f (f X Y) Z) = (f X (f Y Z)).
Axiom right_inverse : forall X : G, (f X (i X)) = e.
Axiom right_unit : forall X : G, (f X e) = X.

Complete associativity right_inverse right_unit : e f i : hint
  for (forall X : G, (f (i X) X) = e).

(* Goal *)
Theorem check : forall X : G, (f (i X) X) = e.
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

