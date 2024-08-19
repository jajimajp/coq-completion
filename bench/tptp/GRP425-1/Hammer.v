(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom single_axiom : forall A B C : G, (multiply (inverse (multiply (inverse (multiply A (inverse (multiply (inverse B) C)))) (multiply A (inverse C)))) (inverse (multiply (inverse C) C))) = B.


(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  hammer.
Qed.

Check check.

