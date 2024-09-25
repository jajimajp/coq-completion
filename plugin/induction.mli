(* only to surpress warnings *)
type operator = { name : string; arity : int }
val  debug_add_single_axiom : unit -> unit Proofview.tactic
module CompletionInput : sig
  type t
  val print : t -> unit
end

val compl_auto : string list -> unit Proofview.tactic
(** [compl_auto fixpoints] returns tactic to complete the fixpoints. *)