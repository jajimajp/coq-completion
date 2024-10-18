From Completion Require Import Plugin.
Require Import Coq.Setoids.Setoid. (* Required by Completion *)

(*** Example 1: Completion and lpo_autorewrite ***)

(* function symbols *)
Parameter G : Set.
Parameter f : G -> G -> G.
Parameter e : G.
Parameter i : G -> G.

(* axioms *)
Axiom associativity : forall a b c, f (f a b) c = f a (f b c).
Axiom left_identity : forall a, f e a = a.
Axiom left_inverse  : forall a, f (i a) a = e.

(* HintDb to register complete rewrite rules *)
Create HintDb my_hint.

(* [Complete <axioms> : <function symbols> : <hint_db>] completes
   given axioms and register complete rewrite rules in <hint_db>. *)
Complete associativity left_identity left_inverse : f e i : my_hint.

(* You can see registered rules using [Print Rewrite HintDb] command. *)
Print Rewrite HintDb my_hint.

(* Proof automation using complete rewrite rules *)
Theorem right_identity : forall a, f a e = a.
Proof.
  (* [lpo_autorewrite with <hint_db>] rewrites current goal using
     rewrite rules in <hint_db> *)
  lpo_autorewrite with my_hint.

  (* The left-hand side and right-hand side are became the same form.
     So you can finish the proof with reflexivity tactic. *)
  reflexivity.
Qed.

(* Note that only the axioms provided to the plugin are being used. *)
Print Assumptions right_identity.

(* You can reuse the HintDb multiple times.
   This saves time on execution. *)
Theorem right_inverse : forall a, f a (i a) = e.
Proof.
  lpo_autorewrite with my_hint.
  reflexivity.
Qed.


(*** Example 2: The [Complete ... for ...] command ***)
(* In addition to axioms, you can specify the equation to prove.
   With this feature, You can give axioms such that
   the completion procedure for the axioms does not terminate. *)

Axiom commutative : forall a b, f a b = f b a.

(* You must use a hint_db different from the one used above 
   to avoid mixing with the previous rewrite rules. *)
Create HintDb hint_comm.

(* The [Complete <axioms> : <function symbols> : <hint_db> for <equation>]
   completes until enough rewrite rules to demonstrate the desired goal
   are obtained. *)
Complete associativity left_identity left_inverse commutative : f e i :
         hint_comm for (forall x y, f x (f (i x) y) = y).

Theorem check : forall x y, f x (f (i x) y) = y.
Proof.
  lpo_autorewrite with hint_comm.
  reflexivity.
Qed.

