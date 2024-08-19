(* Generated by tptp2coqp *)
Require Import Setoid.
From Completion Require Import Plugin.

(* axioms *)
Parameter G : Set.
Axiom moufang1 : forall X Y Z : G, (multiply (multiply X (multiply Y Z)) X) = (multiply (multiply X Y) (multiply Z X)).
Axiom left_inverse : forall X : G, (multiply (left_inverse X) X) = identity.
Axiom left_identity : forall X : G, (multiply identity X) = X.

Complete moufang1 left_inverse left_identity :  : hint
  for ((multiply (multiply (multiply a b) c) b) = (multiply a (multiply b (multiply c b)))).

(* Goal *)
Theorem check : (multiply (multiply (multiply a b) c) b) = (multiply a (multiply b (multiply c b))).
Proof.
  lpo_autorewrite with hint.
  reflexivity.
Qed.

Check check.

