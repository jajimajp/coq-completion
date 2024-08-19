(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom single_axiom : forall A B C D : G, (multiply A (inverse (multiply B (multiply (multiply (multiply C (inverse C)) (inverse (multiply D B))) A)))) = D.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  hammer.
Qed.

Check check.

