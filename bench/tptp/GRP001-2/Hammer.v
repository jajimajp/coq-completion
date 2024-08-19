(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom a_times_b_is_c : (multiply a b) = c.
Axiom squareness : forall X : G, (multiply X X) = identity.
Axiom right_inverse : forall X : G, (multiply X (inverse X)) = identity.
Axiom right_identity : forall X : G, (multiply X identity) = X.
Axiom associativity : forall X Y Z : G, (multiply (multiply X Y) Z) = (multiply X (multiply Y Z)).
Axiom left_inverse : forall X : G, (multiply (inverse X) X) = identity.
Axiom left_identity : forall X : G, (multiply identity X) = X.


(* Goal *)
Theorem check : (multiply b a) = c.
Proof.
  hammer.
Qed.

Check check.

