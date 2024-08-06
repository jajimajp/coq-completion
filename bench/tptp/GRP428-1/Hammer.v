(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom single_axiom : forall A B C D : G, (multiply A (inverse (multiply (multiply (inverse (multiply (inverse B) (multiply (inverse A) C))) D) (inverse (multiply B D))))) = C.


(* Goal *)
Theorem check : (multiply (multiply (inverse b2) b2) a2) = a2.
Proof.
  hammer.
Qed.

Check check.

