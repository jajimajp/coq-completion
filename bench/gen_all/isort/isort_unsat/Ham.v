(* Generated by tptp2coqp *)
Require Import Setoid.
From Hammer Require Import Hammer.

(* axioms *)
Parameter G : Set.
Parameter cons : G -> G -> G.
Parameter false : G.
Parameter insert : G -> G -> G.
Parameter insert_if : G -> G -> G -> G.
Parameter isort : G -> G.
Parameter le : G -> G -> G.
Parameter nil : G.
Parameter s : G -> G.
Parameter true : G.
Parameter z : G.
Axiom insert_if_false : forall L X Y : G, (insert_if false X (cons Y L)) = (cons Y (insert X L)).
Axiom insert_if_true : forall L X Y : G, (insert_if true X (cons Y L)) = (cons X (cons Y L)).
Axiom insert_cons : forall L X Y : G, (insert X (cons Y L)) = (insert_if (le X Y) X (cons Y L)).
Axiom insert_nil : forall X : G, (insert X nil) = (cons X nil).
Axiom isort_cons : forall L X : G, (isort (cons X L)) = (insert X (isort L)).
Axiom isort_nil : (isort nil) = nil.
Axiom le_s_s : forall X Y : G, (le (s X) (s Y)) = (le X Y).
Axiom le_s_z : forall X : G, (le (s X) z) = false.
Axiom le_z : forall Y : G, (le z Y) = true.


(* Goal *)
Theorem check : (isort (cons (s (s z)) (cons (s (s (s z))) (cons (s z) nil)))) = (cons (s z) (cons (s (s z)) (cons (s (s (s z))) nil))).
Proof.
  hammer.
Qed.

Check check.

