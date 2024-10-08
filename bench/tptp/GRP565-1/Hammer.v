(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter a1 : G.
Parameter double_divide : G -> G -> G.
Parameter identity : G.
Parameter inverse : G -> G.
Parameter multiply : G -> G -> G.
Axiom ax_identity : forall A : G, identity = (double_divide A (inverse A)).
Axiom ax_inverse : forall A : G, (inverse A) = (double_divide A identity).
Axiom ax_multiply : forall A B : G, (multiply A B) = (double_divide (double_divide B A) identity).
Axiom ax_single_axiom : forall A B C : G, (double_divide (double_divide A (double_divide (double_divide B (double_divide A C)) (double_divide identity C))) (double_divide identity identity)) = B.


(* Goal *)
Theorem check : (multiply (inverse a1) a1) = identity.
Proof.
  hammer.
Qed.

Check check.

