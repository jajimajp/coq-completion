open My_term

type termid = string

type procedure = strat proof list * rule list * order_param (* (proofs for all rules, completed rules) *)
and procedure_for_goal = strat proof list * goal_strat * order_param (* proofs for proving given goal *)
and goal_strat = rule * termid list (* same as strat.Simp *)
and rule = termid * eq
and eq = term * term
and 'strat proof = (rule * 'strat)
and strat =
  | Axiom
  (* Critical pair between [rule1] and [rule2] with superposition [term]. *)
  | Crit of rule * rule * term
  (* [Simp (r, l)] simplify r by rewriting with [l] *)
  | Simp of rule * termid list

(* example: ["a"; "b"; "c"] implies a > b > c *)
and order_param = string list

val print_proofs : strat proof list -> unit
val print_procedure : procedure -> unit

val parse : string list -> procedure

val parse_for_goal : string list -> procedure_for_goal

(** [add_prefix procedure prefix] adds prefix to rule names. *)
val add_prefix : procedure -> string -> procedure
val add_prefix_proc_for_goal : procedure_for_goal -> string -> procedure_for_goal