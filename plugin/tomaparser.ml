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
| Axioms of tomarule list
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

let readaxioms lines =
  let rec aux lines acc = (* 規則、残りの行 *)
    match lines with
    | line :: rest -> begin
      if line = "" then aux rest acc else
      match String.sub line 0 2 with
      | "ax" -> aux rest acc
      | "in" -> acc, lines (* interreduce の開始 *)
      | _ -> (aux rest ((parsetomarule line) :: acc))
    end
    | [] -> (acc, [])
    in
    let (rules, restlines) = aux lines [] in
    (Axioms (List.rev rules), restlines)

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
      | "ax" ->
        let result, rest = readaxioms lines in
        aux rest (result :: acc)
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
      | Axioms _ -> aux tl proved
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
 

module V6 = struct
  type procedure = strat proof list * rule list (* (proofs for all rules, completed rules) *)
  and rule = termid * eq
  and eq = term * term
  and 'strat proof = (rule * 'strat)

  and strat =
    | Axiom
    (* Critical pair between [rule] and [rule] with superposition [term]. *)
    | Crit of rule * rule * term
    (* [Simp (r, l1, l2)] simplify r by rewriting lhs with [l1], and rhs with [l2] *)
    | Simp of rule * termid list
  
  and minimal_strat =
    | MAxiom
    (* Critical pair between [rule] and [rule] with superposition [term]. *)
    | MCrit of termid * termid * term
    (* [Simp (r, l1, l2)] simplify r by rewriting lhs with [l1], and rhs with [l2] *)
    | MSimp of termid * termid list

  (** [expect str lines] expects [str] as head of lines.
      If head = str, then returns rest lines, raises error otherwise. *)
  let rec expect str lines : string list =
    match lines with
    | hd :: tl ->
      if hd = str then
        tl
      else if hd = "" then
        expect str tl
      else
        failwith ("expect: Unexpected output " ^ hd ^ ", expected " ^ str)
    | _ -> failwith ("expect: Unexpected end of input, expected " ^ str)

  (** [expect_axioms lines] consumes input [lines], returns (lines of axioms, rest lines) *)
  let expect_axioms lines : string list * string list =
    let rec aux lines acc =
      match lines with
      | line :: rest ->
        if line = "generated rules:" then (List.rev acc, lines) else
        aux rest (line :: acc)  
      | [] -> failwith "expect_axioms: reached end of input" in
    aux lines []
  
  (** [consume_proof lines] consumes proof with rule and rest lines if next lines if proof.
      Otherwise returns None with lines unchanged. *)
  let rec consume_proof lines : minimal_strat proof option * string list =
    match lines with
    | [] -> None, []
    | line :: rest ->
      if line = "" then consume_proof rest
      else if line = "ES:" then (None, lines) else
        let parse_header line : rule =
          (* (ex) 49: X6 = +(-(-(X10)), +(-(+(X9, X10)), +(X9, X6))). *)
          let re = Str.regexp "^\\([0-9]+\\): \\(.+\\) \\(->\\|=\\|<-\\) \\(.+\\)\\.$" in
          if Str.string_match re line 0 then
            let id = Str.matched_group 1 line in
            let l = Str.matched_group 2 line in
            let op = Str.matched_group 3 line in
            let r = Str.matched_group 4 line in
            let l = termast_of_string l in
            let r = termast_of_string r in
            match op with
            | "<-" -> (id, (r, l))
            | _ -> (id, (l, r))
          else
            failwith "parse_header: invalid toma rule" in
        let rule = parse_header line in
        let parse_crit line = 
          (* (ex) Proof: A critical pair between equations 2 and 1 with superposition +(+(-(X3), X3), X2). *)
          let re = Str.regexp "^Proof: A critical pair between equations \\([0-9]+\\) and \\([0-9]+\\) with superposition \\(.+\\)\\.$" in
          if Str.string_match re line 0 then
            let id1 = Str.matched_group 1 line in
            let id2 = Str.matched_group 2 line in
            let term = Str.matched_group 3 line in
            let term = termast_of_string term in
            MCrit (id1, id2, term)
          else
            failwith "parse_crit: invalid toma rule" in
        let parse_simp lines : minimal_strat * string list =
          (* (ex) Proof: Rewrite equation 3,
                      lhs with equations []
                      rhs with equations [0]. *)
          begin match lines with
          | l1 :: l2 :: l3 :: rest ->
            let err l = failwith ("parse_simp: invalid toma rule: " ^ l) in
            let re1 = Str.regexp "^Proof: Rewrite equation \\([0-9]+\\),$" in
            if Str.string_match re1 l1 0 then
            let id = Str.matched_group 1 l1 in
            let re2 = Str.regexp ".*lhs with equations \\[\\(.*\\)\\]$" in
            if Str.string_match re2 l2 0 then
            let lids = Str.matched_group 1 l2 |> String.split_on_char ',' in
            let re3 = Str.regexp ".*rhs with equations \\[\\(.*\\)\\].$" in
            if Str.string_match re3 l3 0 then
            let rids = Str.matched_group 1 l3 |> String.split_on_char ',' in
            let ids = lids @ rids in
            (* delete duplicates *)
            let ids = List.sort_uniq compare ids in
            MSimp (id, ids), rest
            else err l3
            else err l2
            else err l1
          | _ -> failwith "parse_simp: unexpected end of input"
          end in
        match (String.split_on_char ' ' (List.hd rest)) with
        | "Proof:" :: "Axiom." :: _ -> Some (rule, MAxiom), (List.tl rest)
        | "Proof:" :: "A" :: "critical" :: _ -> Some (rule, parse_crit (List.hd rest)), (List.tl rest)
        | "Proof:" :: "Rewrite" :: _ ->
          let strat, rest = parse_simp rest in
          Some (rule, strat), rest
        | _ -> failwith ("consume_proof: invalid input: " ^ List.hd rest)

  let expect_completed_rules lines : rule list =
    let parse_rule line : rule =
      (* (ex) 9: +(X4, 0()) -> X4 *)
      let re = Str.regexp "^\\([0-9]+\\): \\(.+\\) -> \\(.+\\)$" in
      if Str.string_match re line 0 then
        let id = Str.matched_group 1 line in
        let l = Str.matched_group 2 line in
        let r = Str.matched_group 3 line in
        let l = termast_of_string l in
        let r = termast_of_string r in
        (id, (l, r))
      else
        failwith "parse_rule: invalid toma rule" in
    let rec aux lines acc =
      match lines with
      | [] -> List.rev acc
      | hd :: tl ->
        if hd = "" then aux tl acc else
          aux tl ((parse_rule hd) :: acc) in
    aux lines []

  let parse_minimal lines = 
    let lines = expect "Completed" lines in
    let lines = expect "axioms:" lines in
    let _, lines = expect_axioms lines in
    let lines = expect "generated rules:" lines in
    let rec aux lines acc : minimal_strat proof list * string list =
      match lines with
      | [] -> List.rev acc, []
      | hd :: tl ->
        match consume_proof lines with
        | None, _ -> List.rev acc, lines
        | Some (rule, strat), rest -> aux rest ((rule, strat) :: acc) in
    let proofs, lines = aux lines [] in
    let lines = expect "ES:" lines in
    let completed_rules = expect_completed_rules lines in
    (proofs, completed_rules)

  let parse lines = 
    let proofs, comp_rules = parse_minimal lines in
    let table = Hashtbl.create 10 in
    List.iter (fun ((id, (l, r)), _) -> Hashtbl.add table id (id, (l, r))) proofs;
    let find id = Hashtbl.find table id in
    let rec aux (proofs : minimal_strat proof list) acc : strat proof list =
      match proofs with
      | [] -> List.rev acc
      | (rule, strat) :: tl ->
        begin match strat with
        | MAxiom -> aux tl ((rule, Axiom) :: acc)
        | MCrit (id1, id2, sp) -> aux tl ((rule, Crit (find id1, find id2, sp)) :: acc)
        | MSimp (id, ids) -> aux tl ((rule, Simp (find id, ids)) :: acc)
        end in
    (aux proofs [], comp_rules)

  let print_procedure (proofs, comp_rules) : unit =
    let rec string_of_term = function
    | Var v -> v
    | App (f, args) -> f ^ "(" ^ (String.concat "," (List.map string_of_term args)) ^ ")" in
    let string_of_rule (id, (l, r)) = id ^ ": " ^ (string_of_term l) ^ " -> " ^ (string_of_term r) in
    let print_proof = function
      | (rule, Axiom) -> print_endline @@ "Axiom: " ^ (string_of_rule rule)
      | (rule, Crit (r1, r2, sp)) -> print_endline @@ "Crit: " ^ (string_of_rule rule) ^ " with " ^ (string_of_rule r1) ^ " and " ^ (string_of_rule r2) ^ " with superposition " ^ (string_of_term sp)
      | (rule, Simp (id, ids)) -> print_endline @@ "Simp: " ^ (string_of_rule rule) ^ " with " ^ (String.concat "," ids) in
    List.iter print_proof proofs;
    let print_rule rule = print_endline @@ "Completed: " ^ (string_of_rule rule) in
    List.iter print_rule comp_rules
end