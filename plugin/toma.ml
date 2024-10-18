(** toma のコマンド実行を関数に隠蔽する *)
module Exe : sig
  val toma : string -> string list
  (** execute with input [string], and return output as [string list] *)

  val toma_with_goal : goal:string -> string -> string list
  val get_toma_version : unit -> string
end = struct
  let write file content =
    let oc = open_out file in
    Printf.fprintf oc "%s" content;
    close_out oc

  let mktemp () =
    let ic = Unix.open_process_in "mktemp" in
    let filename = input_line ic in
    ignore (Unix.close_process_in ic);
    filename

  let file_with_content content =
    let file = mktemp () in
    write file content;
    file

  let input_all_lines ic =
    let rec aux acc =
      try aux (input_line ic :: acc) with End_of_file -> acc
    in
    List.rev (aux [])

  let toma input =
    let argfile = file_with_content input in
    (* tomaへのパスが通っている必要がある *)
    let command = "toma --completion-with-parsable-output " ^ argfile in
    let ic = Unix.open_process_in command in
    let output = input_all_lines ic in
    ignore (Unix.close_process_in ic);
    (* 出力の先頭がリストの後ろに入っているので反転して返す *)
    output

  let toma_with_goal ~goal input =
    let argfile = file_with_content input in
    (* tomaへのパスが通っている必要がある *)
    let command = "toma --parsable \"" ^ goal ^ "\" " ^ argfile in
    print_endline command;
    let ic = Unix.open_process_in command in
    let output = input_all_lines ic in
    ignore (Unix.close_process_in ic);
    (* 出力の先頭がリストの後ろに入っているので反転して返す *)
    output

  let get_toma_version () =
    let command = "toma -h" in
    let ic = Unix.open_process_in command in
    let output = input_all_lines ic in
    ignore (Unix.close_process_in ic);
    match output with
    | [] -> failwith "The toma command was not found. Please install toma and ensure it can be located via the PATH environment variable."
    | h :: _ -> h
end

(** Toma に入力するための TRS 文字列を返す *)
let trs_of ~axioms =
  let variables =
    List.fold_left Devutil.merge [] (List.map Equation.varnames axioms)
  in
  String.concat ""
    [
      "(VAR ";
      String.concat " " variables;
      ")\n";
      "(RULES\n";
      String.concat "\n" (List.map Equation.to_trs_string axioms);
      "\n)\n";
    ]

let acceptable_toma_version = "toma version 0.7+PARSABLE"

let toma axioms =
  let version = Exe.get_toma_version () in
  if not (version = acceptable_toma_version) then
    failwith
      ("VERSION CHECKED: NG : " ^ version ^ "\nexpected: "
     ^ acceptable_toma_version);
  let axioms : Equation.t list = List.map Equation.of_constr axioms in
  Exe.toma (trs_of ~axioms)

let toma_eqs axioms =
  let version = Exe.get_toma_version () in
  if not (version = acceptable_toma_version) then
    failwith
      ("VERSION CHECKED: NG : " ^ version ^ "\nexpected: "
     ^ acceptable_toma_version);
  Exe.toma (trs_of ~axioms)

let toma_with_goal ~goal axioms =
  let version = Exe.get_toma_version () in
  if not (version = acceptable_toma_version) then
    failwith
      ("VERSION CHECKED: NG : " ^ version ^ "\nexpected: "
     ^ acceptable_toma_version);
  let goal = Equation.of_constr goal |> Equation.to_trs_string in
  let axioms : Equation.t list = List.map Equation.of_constr axioms in
  Exe.toma_with_goal ~goal (trs_of ~axioms)
