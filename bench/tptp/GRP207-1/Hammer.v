(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom single_non_axiom : forall U Y Z : G, (multiply U (inverse (multiply Y (multiply (multiply (multiply Z (inverse Z)) (inverse (multiply U Y))) U)))) = U.


(* Goal *)
Theorem check : (multiply x (inverse (multiply y (multiply (multiply (multiply z (inverse z)) (inverse (multiply u y))) x)))) = u.
Proof.
  hammer.
Qed.

Check check.
