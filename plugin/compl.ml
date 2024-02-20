type ruleid = int
type rule =
  ruleid * Equation.t

type t =
  { axioms       : Equation.t list
  ; constants    : string list
  ; hint_db_name : string
  ; proved_rules : rule list
  }

(** Make [t] from values with coq types *)
let make
    ~(axioms:Libnames.qualid list)
    ~(constants:Libnames.qualid list)
    ~(hint_db_name:string)
    : t
  =
  { axioms = List.map Equation.of_qualid axioms
  ; constants = List.map Libnames.string_of_qualid constants
  ; hint_db_name
  ; proved_rules = []
  }

let execute_action
  ~(actions : Tomaparser.proof_action list)
  ~(success_ruleids : ruleid list)
  : Pp.t
      = failwith "not implemented"

let complete ~axioms ~constants ~hint_db_name =
  let t = make ~axioms ~constants ~hint_db_name in
  let _ = t in (* FIXME *)
  let actions, result = (* TODO *) [], Error "not implemented" in
    (* Toma.complete_and_return_actions ~axioms:t.axioms ~constants:t.constants *)
  match result with
  | Ok success_ruleids ->
    execute_action ~actions ~success_ruleids
  | Error err ->
    Pp.str err