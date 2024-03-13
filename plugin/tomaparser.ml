open My_term

type termid = string

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
  let reg = Str.regexp "^\\([^(]+\\)(\\(.*\\))$" in
  match Str.string_match reg str 0 with
  | true ->
    let f = Str.matched_group 1 str in
    let args_str = Str.matched_group 2 str in
    let args_str_list = split_by_comma args_str in
    if args_str_list = [""] then Var f
    else
      let args = List.map termast_of_string args_str_list in
      App (f, args)
  | false -> Var str

type procedure = strat proof list * rule list * order_param (* (proofs for all rules, completed rules) *)
and rule = termid * eq
and eq = term * term
and 'strat proof = (rule * 'strat)
and order_param = string list

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

let expect_order lines : string list * string list =
  match lines with
  | hd :: tl ->
    (* ex: LPO with precedence: ___false > ___true > - > + > 0 *)
    let re = Str.regexp "^LPO with precedence: \\(.*\\)$" in
    if Str.string_match re hd 0 then
      let order = Str.matched_group 1 hd |> Str.split (Str.regexp " > ") in
      (order, tl)
    else
      failwith ("expect_order: Unexpected output " ^ hd)
  | _ -> failwith "expect_order: Unexpected end of input"

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
      let parse_header line : rule * bool = (* (rule, is_reversed(parsed "<-")) *)
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
          | "<-" -> (id, (r, l)), true
          | _ -> (id, (l, r)), false
        else
          failwith "parse_header: invalid toma rule" in
      let rule, rev_lr = parse_header line in
      let parse_crit line = 
        (* (ex) Proof: A critical pair between equations 2 and 1 with superposition +(+(-(X3), X3), X2). *)
        let re = Str.regexp "^Proof: A critical pair between equations \\([0-9]+\\) and \\([0-9]+\\) with superposition \\(.+\\)\\.$" in
        if Str.string_match re line 0 then
          let id1 = Str.matched_group 1 line in
          let id2 = Str.matched_group 2 line in
          let id1, id2 = if rev_lr then id2, id1 else id1, id2 in
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
          let re2 = Str.regexp ".*lhs with equations \\[\\(.+\\)\\]$" in
          let lids = if Str.string_match re2 l2 0 then
            Str.matched_group 1 l2 |> String.split_on_char ','
          else [] in 
          let re3 = Str.regexp ".*rhs with equations \\[\\(.+\\)\\].$" in
          let rids = if Str.string_match re3 l3 0 then
            Str.matched_group 1 l3 |> String.split_on_char ','
          else [] in
          let ids = (lids @ rids) in
          (* delete duplicates *)
          MSimp (id, ids), rest
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
    let re = Str.regexp "^\\([0-9]+\\): \\(.+\\) \\(->\\|=\\|<-\\) \\(.+\\)$" in
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
  let lines = expect "order:" lines in
  let order_param, lines = expect_order lines in
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
  (proofs, completed_rules, order_param)

let parse lines = 
  let proofs, comp_rules, order_param = parse_minimal lines in
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
  (aux proofs [], comp_rules, order_param)

let print_procedure (proofs, comp_rules, order_param) : unit =
  print_endline ("order: " ^ (String.concat " > " order_param));
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