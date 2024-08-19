(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom identity : forall X : G, identity = (double_divide X (inverse X)).
Axiom inverse : forall X : G, (inverse X) = (double_divide X identity).
Axiom multiply : forall X Y : G, (multiply X Y) = (double_divide (double_divide Y X) identity).
Axiom single_axiom : forall X Y Z : G, (double_divide (double_divide X (double_divide (double_divide (double_divide Y X) Z) (double_divide Y identity))) (double_divide identity identity)) = Z.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = identity.
Proof.
  hammer.
Qed.

Check check.

