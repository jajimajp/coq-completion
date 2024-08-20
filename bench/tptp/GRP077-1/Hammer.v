(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter a2 : G.
Parameter a3 : G.
Parameter b3 : G.
Parameter c3 : G.
Parameter double_divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_identity : forall X : G, identity = (double_divide X (inverse X)).
Axiom ax_inverse : forall X : G, (inverse X) = (double_divide X identity).
Axiom ax_multiply : forall X Y : G, (multiply X Y) = (double_divide (double_divide Y X) identity).
Axiom ax_single_axiom : forall X Y Z : G, (double_divide X (double_divide (double_divide (double_divide identity (double_divide (double_divide X identity) (double_divide Y Z))) Y) identity)) = Z.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = identity.
Proof.
  hammer.
Qed.

Check check.

