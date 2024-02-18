(* string の集合 *)
module SS = Set.Make(String)

(* 項 *)
type term =
| Var of string
| App of string * term list (* App (f, [a;b;...]) => f (a, b, ...) *)

(* 等式 (左辺, 右辺) *)
type eq = term * term

(* 項に含まれる変数または定数の集合 *)
let rec idents_in_term (t: term) : SS.t =
  match t with
  | Var name -> SS.singleton name
  | App (_, args) ->
    List.map idents_in_term args
    |> List.fold_left SS.union SS.empty

(* 等式に含まれる変数または定数の集合 *)
let idents_in_eq (eq: eq) : SS.t =
  let l, r = eq in
  SS.union (idents_in_term l) (idents_in_term r)

let rec string_of_term (t: term) =
  match t with
  | Var name -> name
  | App (f, args) ->
      let args = String.concat ", " (List.map string_of_term args) in
      f ^ "(" ^ args ^ ")"

(*
  eq を左辺から右辺への書換規則として string に変換する
  例: "x + e -> x"
*)
let string_of_rewrite_rule (rule: eq) =
  let l, r = rule in
  (string_of_term l) ^ " -> " ^ string_of_term r 

let input_for_toma
  ~(axioms: eq list)
  ~(constants: string list)
  : string =
  let idents_in_axioms = List.fold_left SS.union SS.empty (List.map idents_in_eq axioms) in
  let variables = List.of_seq @@ SS.to_seq @@ SS.diff idents_in_axioms (SS.of_list constants) in
    "(VAR " ^ (String.concat " " variables) ^ ")\n" ^
    "(RULES\n" ^
      (String.concat "\n" (List.map string_of_rewrite_rule axioms)) ^
    "\n)\n"

let rec term_of_constr (c: Constr.t) : term =
  let open Constr in
  match Constr.kind c with
  | Rel i -> Var ("x" ^ string_of_int i)
  | App (f, args) ->
    let args = List.map term_of_constr (Array.to_list args) in
    let f = (match Constr.kind f with
        | Const (k, _) ->
          Names.Constant.to_string k
        | _ -> failwith "Not implemented") in
    App (f, args)
  | Const (k, _) ->
    Var (Names.Constant.to_string k)
  | _ -> failwith "Not implemented"

let rec eq_of_constr
  (c: Constr.t) : eq =
  let open Constr in
  match Constr.kind c with
  | Prod (_, _, t) -> eq_of_constr t (* forall, ... を読み飛ばす *)
  | App (f, args) ->
    let f_is_eq =
      match Constr.kind f with
      | Ind (ind, _) ->
        let (mutind, i) = ind in
        let smut = Names.MutInd.to_string mutind in
        smut = "Coq.Init.Logic.eq"
      | _ -> false in
    if f_is_eq then
      let l = term_of_constr args.(1) in
      let r = term_of_constr args.(2) in
      (l, r)
    else
      failwith "Invalid format of axiom"
  | _ -> failwith "Invalid format of axiom"

(* 各規則をTRS形式にした上で、その他の情報 (RULES, VARS 等) を追加した文字列を返す *)
(* TRS形式への変換では変数名を x0, x1, ... と固定するので、変数の数を数えて VARS を作る *)
let get_toma_input terms =
  let rec max l acc = match l with
    | [] -> acc
    | h :: t -> if h > acc then max t h else max t acc in
  (* 変数の最大個数 *)
  let num_vars = max (List.map (fun t -> List.length (My_term.variables t)) terms) 0 in
  let vars_string_of_num num = (* 例: 3 -> "x1 x2 x3" *)
    let rec loop acc n =
      if n = num then loop ("x" ^ string_of_int n) (n - 1)
      else if n > 0 then
        loop ("x" ^ string_of_int n ^ " " ^ acc) (n - 1) 
      else acc in
    loop "" num in
  let vars_string = vars_string_of_num num_vars in
  let rec string_of_terms = function
    | [] -> ""
    | hd :: tl -> My_term.to_trs hd ^ "\n" ^ (string_of_terms tl) in
  "(VAR " ^ vars_string ^ ")\n" ^
  "(RULES\n" ^ string_of_terms terms ^ ")\n"

(* 一時ファイルをmktempコマンドによって作成し、ファイル名を返す *)
let mktemp () =
  let ic = Unix.open_process_in "mktemp" in
  let rec loop acc =
    try
      let line = input_line ic in loop line
    with
    | End_of_file -> acc
  in
  let result = loop "" in
  ignore (Unix.close_process_in ic);
  result

(* ファイル名 f のファイルに s を書き込む *)
let write f s =
  let oc = open_out f in
  Printf.fprintf oc "%s" s;
  close_out oc

(* argfileをtomaに入力して、tomaの出力を string list で返す *)
let toma_verbose argfile =
  (* tomaへのパスが通っている必要がある *)
  let command = "toma --ordered-completion " ^ argfile ^ " --v" in
  let ic = Unix.open_process_in command in
  let rec loop acc =
    try
      let line = input_line ic in
      let () = print_endline line in (* DEBUG *)
      loop (line :: acc)
    with
    | End_of_file -> acc in
  let res = loop [] in
  ignore (Unix.close_process_in ic);
  (* 出力の先頭がリストの後ろに入っているので反転して返す *)
  List.rev res

let execute_toma terms =
  let tmpfile = mktemp () in
  let _ = write tmpfile (get_toma_input terms) in
  toma_verbose tmpfile

let toma axioms constants =
  let axioms = List.map eq_of_constr axioms in
  let filename = mktemp () in
  let _ = write filename (input_for_toma ~axioms ~constants) in
  toma_verbose filename
