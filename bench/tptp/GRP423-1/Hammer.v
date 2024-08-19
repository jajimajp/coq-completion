(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom single_axiom : forall A B C : G, (inverse (multiply (inverse (multiply A (inverse (multiply (inverse B) (multiply (inverse C) (inverse (multiply (inverse C) C))))))) (multiply A C))) = B.


(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  hammer.
Qed.

Check check.

