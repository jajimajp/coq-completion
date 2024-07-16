(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable and : Z -> Z -> Z.
Variable axiom : Z -> Z.
Variable equivalent : Z -> Z -> Z.
Variable ifeq : Z -> Z -> Z -> Z -> Z.
Variable implies : Z -> Z -> Z.
Variable not : Z -> Z.
Variable or : Z -> Z -> Z.
Variable theorem : Z -> Z.
Variable true : Z.
Axiom equivalent_defn : forall P Q : Z, (equivalent P Q) =? (and (implies P Q) (implies Q P)).
Axiom and_defn : forall P Q : Z, (and P Q) =? (not (or (not P) (not Q))).
Axiom rule_2 : forall X Y : Z, (ifeq (theorem (implies Y X)) true (ifeq (theorem Y) true (theorem X) true) true) =? true.
Axiom rule_1 : forall X : Z, (ifeq (axiom X) true (theorem X) true) =? true.
Axiom implies_definition : forall X Y : Z, (implies X Y) =? (or (not X) Y).
Axiom axiom_1_6 : forall A B C : Z, (axiom (implies (implies A B) (implies (or C A) (or C B)))) =? true.
Axiom axiom_1_5 : forall A B C : Z, (axiom (implies (or A (or B C)) (or B (or A C)))) =? true.
Axiom axiom_1_4 : forall A B : Z, (axiom (implies (or A B) (or B A))) =? true.
Axiom axiom_1_3 : forall A B : Z, (axiom (implies A (or B A))) =? true.
Axiom axiom_1_2 : forall A : Z, (axiom (implies (or A A) A)) =? true.
Axiom ifeq_axiom : forall A B C : Z, (ifeq A A B C) =? B.

Add_lemmas equivalent_defn and_defn rule_2 rule_1 implies_definition axiom_1_6 axiom_1_5 axiom_1_4 axiom_1_3 axiom_1_2 ifeq_axiom.

(* Zoal *)
Theorem check : (theorem (equivalent (and (not p) (not q)) (or p q))) =? true.
Proof.
  smt.
Qed.

Check check.

