(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Axiom multiply : forall A B : G, (multiply A B) = (inverse (double_divide B A)).
Axiom single_axiom : forall A B C : G, (double_divide A (inverse (double_divide (inverse (double_divide (double_divide A B) (inverse C))) B))) = C.


(* Goal *)
Theorem check : (multiply (multiply a3 b3) c3) = (multiply a3 (multiply b3 c3)).
Proof.
  hammer.
Qed.

Check check.

