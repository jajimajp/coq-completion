open My_term

type termid = string

type procedure = strat proof list * rule list (* (proofs for all rules, completed rules) *)
and rule = termid * eq
and eq = term * term
and 'strat proof = (rule * 'strat)
and strat =
  | Axiom
  (* Critical pair between [rule1] and [rule2] with superposition [term]. *)
  | Crit of rule * rule * term
  (* [Simp (r, l)] simplify r by rewriting with [l] *)
  | Simp of rule * termid list

val print_procedure : procedure -> unit

val parse : string list -> procedure