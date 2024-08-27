(** .trs ファイルを Coq の .v ファイルに変換する *)

(* to compile, run: ocamlfind ocamlopt -linkpkg -thread -package core -package str -package ppx_jane trs_to_coq.ml *)
open Core

let escape_name = function
  | "0" -> "zero"
  | "+" -> "plus"
  | "-" -> "minus"
  | "*" -> "times"
  | s -> s

module T = struct
  type t = Var of string | App of string * t list [@@deriving sexp]

  (* トップレベルのカンマで区切る *)
  let split_by_comma s =
    let chars = String.to_list_rev s |> List.rev in
    let rec loop acc l level =
      match l with
      | [] -> [ acc ] (* TODO: 現在0~1個のカンマ直後のスペースにしか対応していない *)
      | ',' :: ' ' :: t | ',' :: t ->
          if level = 0 then acc :: loop [] t level
          else loop (acc @ [ ',' ]) t level
      | '(' :: t -> loop (acc @ [ '(' ]) t (level + 1)
      | ')' :: t -> loop (acc @ [ ')' ]) t (level - 1)
      | h :: t -> loop (acc @ [ h ]) t level
    in
    List.map ~f:String.of_char_list (loop [] chars 0)

  let rec of_string str =
    let str = String.strip str in
    let reg = Str.regexp "^\\([^(]+\\)(\\(.+\\))$" in
    match Str.string_match reg str 0 with
    | true ->
        let f = Str.matched_group 1 str in
        let args_str = Str.matched_group 2 str in
        let args_str_list = split_by_comma args_str in
        let args = List.map ~f:of_string args_str_list in
        App (escape_name f, args)
    | false ->
        if String.contains str ' ' then
          Printf.eprintf "WARNING: space found in variable: \"%s\"\n" str;
        Var (escape_name str)

  let rec iter_vars t ~f =
    match t with
    | Var s -> f s
    | App (_, args) -> List.iter ~f:(fun t -> iter_vars t ~f) args

  let rec iter_idents t ~f =
    match t with
    | Var s -> f s
    | App (fname, args) ->
        f fname;
        List.iter ~f:(fun t -> iter_idents t ~f) args

  let idents t =
    let names = ref [] in
    iter_idents t ~f:(fun s ->
        if List.mem ~equal:String.equal !names s then ()
        else names := s :: !names);
    !names

  let find_argnum t fname =
    let rec loop t =
      match t with
      | Var s -> if String.(fname = s) then Some 0 else None
      | App (f, args) ->
          if String.(f = fname) then Some (List.length args)
          else List.find_map ~f:loop args
    in
    loop t

  let rec to_coq t =
    match t with
    | Var s -> s
    | App (f, args) ->
        let args_str =
          List.map
            ~f:(fun c ->
              match c with Var _ -> to_coq c | App _ -> "(" ^ to_coq c ^ ")")
            args
          |> String.concat ~sep:" "
        in
        Printf.sprintf "%s %s" f args_str
end

module E = struct
  type t = T.t * T.t [@@deriving sexp]

  let of_string str =
    let str = String.strip str in
    let reg = Str.regexp "^\\(.*\\) -> \\(.*\\)$" in
    match Str.string_match reg str 0 with
    | true ->
        let l = Str.matched_group 1 str in
        let r = Str.matched_group 2 str in
        (T.of_string l, T.of_string r)
    | false -> failwith ("E: parse error: " ^ str)

  let iter_vars (l, r) ~f =
    T.iter_vars l ~f;
    T.iter_vars r ~f

  let idents (l, r) =
    List.dedup_and_sort ~compare:String.compare (T.idents l @ T.idents r)

  let find_argnum (l, r) fname =
    match T.find_argnum l fname with
    | Some n -> Some n
    | None -> T.find_argnum r fname

  let to_coq t vars =
    let idents = ref [] in
    iter_vars t ~f:(fun s ->
        if List.mem ~equal:String.equal !idents s then ()
        else idents := s :: !idents);
    let prods =
      List.filter ~f:(fun s -> List.mem ~equal:String.equal vars s) !idents
    in
    let prods = List.rev prods in
    String.concat ~sep:""
      ((if List.length prods > 0 then
          [ "forall "; String.concat ~sep:" " prods; ", " ]
        else [])
      @ [ T.to_coq (fst t); " = "; T.to_coq (snd t); "" ])
end

module Trs = struct
  type t = { var : string list; rules : E.t list } [@@deriving sexp]

  (* (VAR x y z) *)
  let parseVAR line =
    let reg = Str.regexp "^(VAR \\(.*\\))$" in
    match Str.string_match reg line 0 with
    | true ->
        let vars = Str.matched_group 1 line in
        let vars = String.strip vars in
        if String.(vars = "") then []
        else
          let vars = String.split ~on:' ' vars in
          vars
    | false -> failwith "VAR: parse error"

  (* Returns rules and rest lines
     (RULES
      +(0, y) -> y
      +(-(x), x) -> 0
      +(+(x, y), z) -> +(x, +(y, z))
      )
  *)
  let parseRULES lines =
    match lines with
    | hd :: rest ->
        if String.is_prefix hd ~prefix:"(RULES" then
          let rec loop acc rest =
            match rest with
            | ")" :: t -> (acc, t)
            | h :: t -> loop (h :: acc) t
            | [] -> failwith "RULES: parse error: []"
          in
          let rules, rest = loop [] rest in
          let rules =
            List.filter ~f:(fun s -> String.length (String.strip s) > 0) rules
          in
          (List.map ~f:E.of_string rules, rest)
        else failwith "RULES: parse error: not (RULES"
    | _ -> failwith "RULES: parse error: not (RULES"

  let parse lines =
    let rec loop acc lines =
      match lines with
      | [] -> acc
      | hd :: tl -> (
          if String.length hd < 4 then loop acc tl
          else
            match String.sub hd ~pos:0 ~len:4 with
            | "(VAR" ->
                if List.length acc.var > 0 then
                  Printf.eprintf
                    "WARNING: multiple VAR lines found in .trs file. This may \
                     cause unexpected behavior.";
                loop { acc with var = parseVAR hd } tl
            | "(RUL" ->
                let rules, rest = parseRULES lines in
                loop { acc with rules } rest
            | _ ->
                Printf.eprintf "INFO: ignoring line: %s\n" hd;
                loop acc tl)
    in
    loop { var = []; rules = [] } lines

  let to_coq t =
    let funnames =
      List.map ~f:E.idents t.rules
      |> List.concat
      |> List.filter ~f:(fun s -> not (List.mem ~equal:String.equal t.var s))
      |> List.dedup_and_sort ~compare:String.compare
    in
    let argnum_of_funname fname =
      List.find_map ~f:(fun e -> E.find_argnum e fname) t.rules
      |> Option.value_exn
    in
    let functions =
      funnames
      |> List.map ~f:(fun s ->
             let argnum = argnum_of_funname s in
             String.concat ~sep:""
               [
                 "Parameter ";
                 s;
                 " : ";
                 String.concat ~sep:" -> "
                   (List.init (argnum + 1) ~f:(fun _ -> "G"));
                 ".";
               ])
      |> String.concat ~sep:"\n"
    in
    let axioms =
      List.mapi
        ~f:(fun i r ->
          "Axiom ax" ^ string_of_int i ^ " : " ^ E.to_coq r t.var ^ ".")
        t.rules
      |> String.concat ~sep:"\n"
    in
    let axiom_names =
      List.mapi ~f:(fun i _ -> "ax" ^ string_of_int i) t.rules
    in
    String.concat ~sep:"\n"
      [
        {|
Require Import Coq.Setoids.Setoid.
From Completion Require Import Plugin.

Parameter G : Set.
    |};
        functions;
        axioms;
        "Create HintDb hint_compl.";
        String.concat ~sep:""
          [
            "Complete ";
            String.concat ~sep:" " axiom_names;
            " : ";
            String.concat ~sep:" " funnames;
            " : hint_compl.";
          ];
        "Print Rewrite HintDb hint_compl.";
      ]
end

let print_comments filepath lines =
  let filename = Filename.basename filepath in
  String.concat ~sep:"\n"
    ([
       "(*";
       "This example was automatically generated by converting from";
       filename ^ ": ";
       "";
     ]
    @ lines @ [ ""; "*)" ])
  |> Printf.printf "%s\n"

let parse_files files =
  let rec loop files =
    match files with
    | [] -> ()
    | hd :: tl ->
        let lines = In_channel.read_lines hd in
        let trs = Trs.parse lines in
        print_comments hd lines;
        Printf.printf "%s\n" (Trs.to_coq trs);
        loop tl
  in
  loop files

let () =
  let files = ref [] in
  Array.iteri
    ~f:(fun i arg -> if i > 0 then files := arg :: !files)
    (Sys.get_argv ());
  let files = List.rev !files in
  parse_files files
