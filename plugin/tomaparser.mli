module Completion : sig
  type ruleid
  type rule = ruleid * Equation.t

  (** Strategies to prove rules. *)
  type proof_strat =
     (* Immediately proved by one of axioms *)
    | ByAxiom
     (* By critial-pair of [rule1] and [rule2] with superposition [term] *)
    | CriticalPairs of rule * rule * Equation.Term.t
     (* Reduce rebundant rule([ruleid]) by rules *)
    | Reduction of ruleid * ruleid list

  (** Algorithm state *)
  type state

  val init :
    constants:string list -> axioms:rule list -> state

  (** Possible actions in completion steps. *)
  type action =
     (* Prove rule with strategy [proof_strat] *)
    | Prove of rule * proof_strat
     (* Terminate steps with completed [rules] *)
    | Terminate of ruleid list
     (* Failure of steps with reason [string] *)
    | Fail of string

  val execute_proof : state -> rule -> proof_strat -> state
end

type proof_action =
  Completion.ruleid * Equation.t * Completion.proof_strat

open My_term

type termid = string

(* 規則の番号, 左辺, 右辺 *)
type tomarule = termid * term * term

type tomaoutputsection =
| ReductionOrder of tomarule list
  (* 新しい規則, criticalpairs の規則１、規則２、superposition *)
| CriticalPairs of (tomarule * termid * termid * term) list
  (* 規則1, 規則2, 書換に使った規則のリスト - 規則１をinterreduceして規則２を得る *)
| Interreduce of (tomarule * tomarule * termid list) list
  (* 最終的な規則一覧 *)
| TerminationSuccess of tomarule list

val describe_toma_output : string list -> unit

val readtomaoutput : string list -> tomaoutputsection list
