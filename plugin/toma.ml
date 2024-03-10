(** toma のコマンド実行を関数に隠蔽する *)
module Exe : sig
  (** execute with input [string], and return output as [string list] *)
  val toma : string -> string list
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
      try
        aux ((input_line ic) :: acc)
      with
        End_of_file -> acc in
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

  let get_toma_version () =
    let command = "toma -h" in
    let ic = Unix.open_process_in command in
    let output = input_all_lines ic in
    ignore (Unix.close_process_in ic);
    List.hd output
end

(** Toma に入力するための TRS 文字列を返す *)
let trs_of ~axioms =
  let variables = List.fold_left Devutil.merge [] (List.map Equation.varnames axioms) in
  String.concat ""
  [ "(VAR "; String.concat " " variables; ")\n";
    "(RULES\n";
    String.concat "\n" (List.map Equation.to_trs_string axioms);
    "\n)\n" ]

let toma axioms = 
  let version =  Exe.get_toma_version () in
  if not (version = "toma version 0.6+PARSABLE") then
    failwith ("VERSION CHECKED: NG : " ^ version);
  let axioms : Equation.t list = List.map Equation.of_constr axioms in
  Exe.toma (trs_of ~axioms)