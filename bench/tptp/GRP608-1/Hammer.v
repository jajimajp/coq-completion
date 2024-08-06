(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter double_divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom multiply : forall A B : G, (multiply A B) = (inverse (double_divide B A)).
Axiom single_axiom : forall A B C : G, (double_divide (inverse (double_divide A (inverse (double_divide (inverse B) (double_divide A C))))) C) = B.


(* Goal *)
Theorem check : (multiply a b) = (multiply b a).
Proof.
  hammer.
Qed.

Check check.

