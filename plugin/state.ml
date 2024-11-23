(** Manage global state using summary *)

type state =
  { set_name : string (* like "G" *)
  ; order_params : string list
  }

let state : (string * state) list ref = Summary.ref ~name:"state" []

let register db_name st =
  state := (db_name, st) :: !state

let _cur_set_name : string option ref = ref None
let _cur_order_params : string list option ref = ref None

let broadcast db_name =
  match List.assoc_opt db_name !state with
  | None -> failwith "Invalid HintDb was used. Ensure the HintDb was given to the Complete command."
  | Some { set_name; order_params } ->
    _cur_set_name := Some set_name;
    _cur_order_params := Some order_params

let current_set_name () = match !_cur_set_name with
  | None -> failwith "Internal error. This error often occurs when you run lpo_autorewrite without executing Complete command."
  | Some name -> name

let current_order_params () = match !_cur_order_params with
  | None -> failwith "Internal error: LPO order could not be obtained. This error often occurs when you run lpo_autorewrite without executing Complete command."
  | Some o -> o

