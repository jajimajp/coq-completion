(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom single_axiom : forall A B C D : G, (multiply A (inverse (multiply B (multiply C (multiply (multiply (inverse C) (inverse (multiply D B))) A))))) = D.


(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  hammer.
Qed.

Check check.

