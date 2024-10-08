(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter b1 : G.
Parameter double_divide : G -> G -> G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_multiply : forall A B : G, (multiply A B) = (inverse (double_divide B A)).
Axiom ax_single_axiom : forall A B C D : G, (double_divide (double_divide A (inverse (double_divide B C))) (double_divide (inverse B) (inverse (double_divide D (double_divide A D))))) = C.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = (multiply (inverse b1) b1).
Proof.
  hammer.
Qed.

Check check.

