(** Return next int * int value to enumerate all int pairs.
    {4 Examples}
    {[next_int_pairs (1, 2)]} (2, 2) *)
let next_int_pairs (prev: int * int) : int * int =
  let (x, y) = prev in
  if y = 1 then (1, x + 1)
  else if x < y then (x + 1, y)
  else (x, y - 1)

module Completion = struct
  type ruleid = int
  type rule = ruleid * Equation.t

  let rulename (ruleid, _ : rule) : string =
    "t" ^ string_of_int ruleid

  type proof_strat =
    | ByAxiom
    | CriticalPairs of rule * rule * Equation.Term.t
    | Reduction of ruleid * ruleid list

  type state =
    { constants : string list
    ; axioms : rule list
    ; proved_rules : rule list
    }

  let init ~constants ~axioms = { constants; axioms; proved_rules = [] }

  type action =
    | Prove of rule * proof_strat
    | Terminate of ruleid list
    | Fail of string

  (** Proof [goal] by critical-pairs of [rule1] and [rule2]
      with superposition [sup] *)
  let execute_proof_using_crit
    : state -> rule -> rule -> rule -> Equation.Term.t -> unit
    = fun st goal rule1 rule2 sup ->
      let module E = Equation in
      let open Rewrite in
      let open Equality in
      let open Tactypes in
      let env = Global.env () in
      let sigma = Evd.from_env env in
      let (sigma, hyp1) =
        Constrintern.interp_constr_evars env sigma
          (E.create_with_constants
             ~constants:st.constants
             ~left:sup
             ~right:(E.left (snd goal))
           |> E.to_constr_expr) in
      let (sigma, hyp2) =
        Constrintern.interp_constr_evars env sigma
          (E.create_with_constants
             ~constants:st.constants
             ~left:sup
             ~right:(E.left (snd goal))
           |> E.to_constr_expr) in
      let rewriteLR rulename at =
        cl_rewrite_clause
          (fun env sigma -> sigma, (
               (EConstr.mkRef (Nametab.global (Libnames.qualid_of_string rulename), EConstr.EInstance.empty)),
               NoBindings))
          true
          (OnlyOccurrences [at]) None in
      let rewrite_with_binds ~l2r in_hyp vars =
        let explicit_bind v = CAst.make (NamedHyp (CAst.make (Names.Id.of_string v)), (EConstr.mkVar (Names.Id.of_string v))) in
        let binds = ExplicitBindings (List.map explicit_bind vars) in
        general_rewrite
          ~where:None ~l2r (OnlyOccurrences [1]) ~freeze:true ~dep:true ~with_evars:false
          (EConstr.mkVar (Names.Id.of_string in_hyp), binds) in
      let tactic_with (at1 : int) (at2 : int) =
        let open Proofview.Notations in
        Tactics.assert_by
          Names.Name.Anonymous
          hyp1
          (Tactics.intros <*>
           rewriteLR (rulename rule1) at1 <*>
           Tactics.reflexivity) <*>
        Tactics.assert_by
          Names.Name.Anonymous
          hyp2
          (Tactics.intros <*>
            rewriteLR (rulename rule2) at2 <*>
            Tactics.reflexivity) <*>
        Tactics.intros <*>
        rewrite_with_binds ~l2r:false "H" (E.varnames (snd rule1)) <*>
        rewrite_with_binds ~l2r:true "H1" (E.varnames (snd rule2)) <*>
        Tactics.reflexivity in
      let name = rulename goal |> Names.Id.of_string in
      let (sigma, body) = Constrintern.interp_constr_evars env sigma (Equation.to_constr_expr (snd goal)) in
      let typ = EConstr.to_constr sigma body in
      let info = Declare.Info.make ~poly:false () in
      let cinfo = Declare.CInfo.make ~name ~typ () in
      let (t, types, ustate, obl_info) = Declare.Obls.prepare_obligation ~name ~types:None ~body sigma in
      let rec loop (at1, at2) =
        let tactic = tactic_with at1 at2 in
        let _, progress = Declare.Obls.add_definition ~pm:(Declare.OblState.empty) ~cinfo ~info ~uctx:ustate ~tactic obl_info in
        match progress with
        | Defined _ -> ()
        | _ -> loop (next_int_pairs (at1, at2)) in
      loop (1, 1)

  let execute_proof state rule strat =
    match strat with
    | CriticalPairs (rule1, rule2, sup) ->
      execute_proof_using_crit state rule rule1 rule2 sup;
      { state with proved_rules = rule :: state.proved_rules }
    | _ -> failwith "not implemented"
end

type proof_action =
  Completion.ruleid * Equation.t * Completion.proof_strat

open My_term

type termid = string

(* 規則の番号, 左辺, 右辺 *)
type tomarule = termid * term * term

let string_of_chars (l : char list) =
  l |> List.to_seq |> String.of_seq

let split_by_comma s =
  let l = List.of_seq (String.to_seq s) in
  let rec loop acc l level =
    match l with
    | [] -> [acc]
      (* TODO: 現在0~1個のカンマ直後のスペースにしか対応していない *)
    | ',' :: ' ' :: t | ',' :: t ->
      if (level = 0) then acc :: (loop [] t level)
      else loop (acc @ [',']) t level
    | '(' :: t -> loop (acc @ ['(']) t (level + 1)
    | ')' :: t -> loop (acc @ [')']) t (level - 1)
    | h :: t -> loop (acc @ [h]) t level in
  List.map string_of_chars (loop [] l 0)

let rec termast_of_string str =
  let reg = Str.regexp "^\\([^(]+\\)(\\(.+\\))$" in
  match Str.string_match reg str 0 with
  | true ->
    let f = Str.matched_group 1 str in
    let args_str = Str.matched_group 2 str in
    let args_str_list = split_by_comma args_str in
    let args = List.map termast_of_string args_str_list in
    App (f, args)
  | false -> Var str

let string_of_termast term =
  let rec aux term =
    match term with
    | Var v -> "Var{" ^ v ^ "}"
    | App (func, args) ->
      let args = List.map aux args in
      "App{" ^ func ^ ",[" ^ String.concat ";" args ^ "]}"
  in aux term

type tomaoutputsection =
| ReductionOrder of tomarule list
  (* 新しい規則, criticalpairs の規則１、規則２、superposition *)
| CriticalPairs of (tomarule * termid * termid * term) list
| Interreduce of (tomarule * tomarule * termid list) list
  (* 最終的な規則一覧 *)
| TerminationSuccess of tomarule list
  (* 手続きの失敗 *)
(* | TerminationError *)

let parsetomarule line : tomarule =
  let re = Str.regexp "^\\([0-9]+\\): \\(.+\\) -> \\(.+\\)$" in
  if Str.string_match re line 0 then
    let id = Str.matched_group 1 line in
    let left = Str.matched_group 2 line in
    let right = Str.matched_group 3 line in
    (* NOTE: termast_of_string を上で呼ぶと string_match が汚染されてバグが生じる *)
    let left = termast_of_string left in
    let right = termast_of_string right in
    (id, left, right)
  else
    failwith "not match toma rule"

let parsetomaruleopt line : tomarule option =
  let re = Str.regexp "^\\([0-9]+\\): \\(.+\\) -> \\(.+\\)$" in
  if Str.string_match re line 0 then
    let id = Str.matched_group 1 line in
    let left = Str.matched_group 2 line in
    let right = Str.matched_group 3 line in
    (* NOTE: termast_of_string を上で呼ぶと string_match が汚染されてバグが生じる *)
    let left = termast_of_string left in
    let right = termast_of_string right in
    Some (id, left, right)
  else
    None

let readreductionorder lines =
  let rec aux lines acc = (* 規則、残りの行 *)
    match lines with
    | line :: rest -> begin
      if line = "" then aux rest acc else
      match String.sub line 0 2 with
      | "re" | "LP" | "ES" -> aux rest acc
      | "cr" -> acc, lines (* critical pairs: の開始 *)
      | _ -> (aux rest ((parsetomarule line) :: acc))
    end
    | [] -> (acc, [])
    in
    let (rules, restlines) = aux lines [] in
    (ReductionOrder (List.rev rules), restlines)

let parsecriticalpair line =
  let re = Str.regexp "^\\([0-9]+\\): \\(.+\\) = \\(.+\\)\\.$" in
  if Str.string_match re line 0 then
    let id = Str.matched_group 1 line in
    let left = Str.matched_group 2 line in
    let right = Str.matched_group 3 line in
    (* NOTE: termast_of_string を上で呼ぶと string_match が汚染されてバグが生じる *)
    let left = termast_of_string left in
    let right = termast_of_string right in
    (id, left, right)
  else
    failwith @@ "not match toma rule (critical pairs) for " ^ line

let parseproof line =
  let re = Str.regexp "^Proof: A critical pair between equations \\([0-9]+\\) and \\([0-9]+\\) with superposition \\(.*\\)\\.$" in
  if Str.string_match re line 0 then
    let id1 = Str.matched_group 1 line in
    let id2 = Str.matched_group 2 line in
    let term = Str.matched_group 3 line in
    let term = termast_of_string term in
    (id1, id2, term)
  else
    failwith "not match toma rule p"

let parse_used_termids s =
  Str.split (Str.regexp ",") s

let parseinterreduce line =
  let re = Str.regexp "^\\([0-9]+\\): interreduce \\([0-9]+\\):\\(.+\\) = \\(.+\\) to get \\([0-9]+\\):\\(.+\\) = \\(.+\\) using \\[\\(.*\\)\\]$" in
  if Str.string_match re line 0 then
    let prev_id = Str.matched_group 2 line in
    let next_id = Str.matched_group 1 line in
    let prev_left = Str.matched_group 3 line in
    let prev_right = Str.matched_group 4 line in
    let next_left = Str.matched_group 6 line in
    let next_right = Str.matched_group 7 line in
    let used_termids = Str.matched_group 8 line in
    let prev_left = termast_of_string prev_left in
    let prev_right = termast_of_string prev_right in
    let next_left = termast_of_string next_left in
    let next_right = termast_of_string next_right in
    let used_termids = parse_used_termids used_termids in
    ((prev_id, prev_left, prev_right), (next_id, next_left, next_right), used_termids)
  else
    failwith "not match toma rule interreduce"

let readterminationsuccess lines =
  let rec aux lines acc =
    match lines with
    | [] -> acc
    | line :: rest -> begin
      match parsetomaruleopt line with
        | None -> aux rest acc
        | Some rule -> aux rest (rule :: acc)
    end
  in
  let result = aux lines [] in
  TerminationSuccess (List.rev result)

let readcriticalpairs lines =
  let rec aux lines acc =
    match lines with
    | [] -> acc, []
    | line :: rest -> begin
      if line = "" then aux rest acc else
        match String.sub line 0 2 with
        | "cr" -> aux rest acc (* 読み飛ばし *)
        | "in" -> acc, lines (* interreduce: の開始 *)
        | "YE" -> acc, rest (* 手続きの完了 *)
        | _ -> begin
          match rest with
          | [] -> failwith "invalid input: no proof under critical pair"
          | secondline :: rest ->
            let rule = parsecriticalpair line in
            let (id1, id2, t) = parseproof secondline in
            aux rest ((rule, id1, id2, t) :: acc)
      end
    end
  in
  let (result, restlines) = (aux lines []) in
  match result with
  | [] -> (* critical pair が見つからなかったときは手続きの終了 *)
    (readterminationsuccess restlines, [])
  | _ -> (CriticalPairs (List.rev result), restlines)

let readinterreduce lines =
  let rec aux lines acc =
    match lines with
    | [] -> acc, []
    | line :: rest -> begin
      if line = "" then aux rest acc else
        match String.sub line 0 2 with
        | "in" -> aux rest acc (* 読み飛ばし *)
        | "re" -> acc, lines (* reduction order: の開始 *)
        | _ ->
          let record = parseinterreduce line in
          aux rest (record :: acc)
        end in
  let (result, restlines) = (aux lines []) in
  Interreduce (List.rev result), restlines

let readtomaoutput lines =
  let rec aux lines acc =
    match lines with
    | [] -> acc
    | line :: rest -> begin
      if line = "" then aux rest acc else
      match String.sub line 0 2 with
      | "re" ->
        let result, rest = readreductionorder lines in
        aux rest (result :: acc)
      | "cr" ->
        let result, rest = readcriticalpairs lines in
        aux rest (result :: acc)
      | "in" ->
        let result, rest = readinterreduce lines in
        aux rest (result :: acc)
      | _ ->
        aux rest acc
    end
  in
  List.rev (aux lines [])


module Strset = Set.Make(String)

let describereductionorder entry proved =
  match entry with
  | ReductionOrder r ->
    let rec aux rules proved =
      match rules with
      | [] -> proved
      | (termid, left, right) :: tl ->
        if Strset.mem termid proved then
          aux tl proved
        else
          let _ = print_endline @@ "Prove " ^ termid ^ ": " ^ (string_of_termast left) ^ " = " ^ (string_of_termast right) ^ " using Autorewrite." in
          let proved = Strset.add termid proved in
          aux tl proved
        in aux r proved
  | _ -> failwith "invalid input"

let describecriticalpairs entry proved =
  match entry with
  | CriticalPairs c ->
    let rec aux rules proved =
      match rules with
      | [] -> proved
      | ((id, left, right), id1, id2, term) :: tl ->
        let left = string_of_termast left in
        let right = string_of_termast right in
        let term = string_of_termast term in
        let _ = print_endline @@ "Prove " ^ id ^ ": " ^ left ^ " = " ^ right ^ ":" in
        let _ = print_endline @@ " - " ^ "assert " ^ term ^ " = " ^ left ^ " by rule " ^ id1 in
        let _ = print_endline @@ " - " ^ "assert " ^ term ^ " = " ^ right ^ " by rule " ^ id2 in
        let proved = Strset.add id proved in
          aux tl proved
        in aux c proved
        | _ -> failwith "invalid input"

let describeinterreduce entry proved =
  match entry with
  | Interreduce c ->
    let rec aux rules proved =
      match rules with
      | [] -> proved
      | ((id1, left1, right1), (id2, left2, right2), _) :: tl ->
        let left1 = string_of_termast left1 in
        let right1 = string_of_termast right1 in
        let left2 = string_of_termast left2 in
        let right2 = string_of_termast right2 in
        let _ = print_endline @@ "Prove interreduce " ^ id2 ^ ": " ^ left2 ^ " = " ^ right2 ^ ":" in
        let _ = print_endline @@ " - " ^ "assert " ^ left1 ^ " = " ^ right1 ^ " -> " ^ left2 ^ " = " ^ right2 ^ " by rule " ^ id1 in
        let proved = Strset.add id2 proved in
          aux tl proved
        in aux c proved
        | _ -> failwith "invalid input"

let describe out =
  let rec aux out proved =
    match out with
    | [] -> ()
    | hd :: tl -> begin match hd with
      | ReductionOrder _ ->
          let proved = describereductionorder hd proved in
          aux tl proved
      | CriticalPairs _ ->
          let proved = describecriticalpairs hd proved in
          aux tl proved
      | Interreduce _ ->
          let proved = describeinterreduce hd proved in
          aux tl proved
      | TerminationSuccess rules -> (print_endline "\nSuccess.\nResult:";
      ignore @@ List.map (fun (id, left, right) -> print_endline @@ id ^ ": " ^ (string_of_termast left) ^ " -> " ^ (string_of_termast right)) rules; aux tl proved)
      (* | TerminationError -> (print_endline "Fail."; aux tl proved) *)
    end
  in aux out (Strset.of_list ["0"; "1"; "2"]) (* TODO: hard coded *)

let describe_toma_output lines =
  let output = readtomaoutput lines in
  describe output

(*
let read_file filename = 
  let lines = ref [] in
  let chan = open_in filename in
  try
    while true; do
      lines := input_line chan :: !lines
    done; !lines
  with End_of_file ->
    close_in chan;
    List.rev !lines ;;

let _ = 
  let lines = read_file "/Users/yajima/h/coq/doc/plugin_tutorial/knuth/misc/toma-v.txt" in
  ignore @@ describe_toma_output lines
*)
 
