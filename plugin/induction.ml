open My_term

let label_of_constr =
  let open Constr in function
  | Rel _ -> "Rel"
  | Var _ -> "Var"
  | Meta _ -> "Meta"
  | Evar _ -> "Evar"
  | Sort _ -> "Sort"
  | Cast (_, _, _) -> "Cast"
  | Prod (_, _, _)-> "Prod"
  | Lambda (_, _, _) -> "Lambda"
  | LetIn (_, _, _, _) -> "LetIn"
  | App (_, _) -> "App"
  | Const _ -> "Const"
  | Ind _-> "Ind"
  | Construct _ -> "Construct"
  | Case (_, _, _, _, _, _, _) -> "Case"
  | Fix _ -> "Fix"
  | CoFix _ -> "CoFix"
  | Proj (_, _)-> "Proj"
  | Int _ -> "Int"
  | Float _ -> "Float"
  | Array (_, _, _, _)-> "Array"

type operator = { name : string; arity : int }
(* leave this for debug printing *)
(*
let operators_dbg env sigma (t : Evd.econstr) : operator list =
  let open Constr in
  let open EConstr in
  (* operators in each variants (without rec) *)
  let rec aux acc t = match EConstr.kind sigma t with
    | Ind (inductive, instance) ->
        let (mutind, pos) = inductive in
        let ppind = Pp.(str "<Inductive '" ++ Names.MutInd.print mutind ++ str " at position " ++ int pos ++ str ">") in
        Feedback.msg_notice Pp.(str "Ind: " ++
        ppind ++
        str "<Instance: " ++ Univ.Instance.pr UnivNames.pr_with_global_universes (EInstance.kind sigma instance) ++ str ">"
        );
        acc
    | Construct (constructor, instance) ->
        let (ind, pos) = constructor in
        let (mutind, mutindpos) = ind in
        let cases = ComInductive.make_cases ind in
        List.iter (fun l -> Printf.printf "<>"; List.iter (Printf.printf "Got: %s\n") l) cases;
        let ppind = Pp.(str "<Inductive '" ++ Names.MutInd.print mutind ++ str " at position " ++ int mutindpos ++ str ">") in
        let ppconstr = Pp.(str "<Construct at position " ++ int pos ++ str ">" ++ ppind ++ str"</Construct>") in
        Feedback.msg_notice Pp.(str "Construct: " ++
        ppconstr ++
        str "<Instance: " ++ Univ.Instance.pr UnivNames.pr_with_global_universes (EInstance.kind sigma instance) ++ str ">"
        );
        acc
    | App (f, arg_arr) -> begin
        Feedback.msg_notice Pp.(str "<App>");
        if isConst sigma f then (
          let (constant, einstance) = destConst sigma f in
          (* args are not folded in EConstr.fold *)
          ignore @@ Array.map (aux acc) arg_arr;

          (* lookup def *)
          let constant_body = Environ.lookup_constant constant env in
          let _ = (match constant_body.const_body with
          | Def constr -> begin
              Feedback.msg_notice Pp.(str "Def" ++ Printer.pr_constr_env env sigma constr)
            end
          | _ -> print_endline "NG") in

          Feedback.msg_notice Pp.(Names.Constant.print constant ++ str ", args: len " ++ int (Array.length arg_arr) ++
          str "</App>"
          );
          acc)
        else if isConstruct sigma f then (
          let (constructor, einstance) = destConstruct sigma f in
          let (ind, pos) = constructor in
          let (mutind, mutindpos) = ind in
          let ppind = Pp.(str "<Inductive '" ++ Names.MutInd.print mutind ++ str " at position " ++ int mutindpos ++ str ">") in
          let ppconstr = Pp.(str "<Construct at position " ++ int pos ++ str ">" ++ ppind ++ str"</Construct>") in
          ignore @@ Array.map (aux acc) arg_arr;
          Feedback.msg_notice Pp.(ppconstr ++ str ", args: len " ++ int (Array.length arg_arr) ++
          str "<Instance: " ++ Univ.Instance.pr UnivNames.pr_with_global_universes (EInstance.kind sigma einstance) ++ str ">" ++
          str "</App>"
          );
          acc)
        else (
          (* failwith (Printf.sprintf "App: Function should be constant. %s is not supported." (label_of_constr (EConstr.kind sigma f))) *)
          Feedback.msg_notice Pp.(str "</App>");
          acc)
      end
    | Var id -> Feedback.msg_notice Pp.(str "<Var " ++ (Names.Id.print id) ++ str ">"); acc
    | t -> failwith ("Not implemented: " ^ label_of_constr t) in
  fold sigma aux [] t
*)

module CompletionInput = struct
  type t =
    { set : string option (* Set *)
    ; ops : (string * int) list (* function operators (name, arity), arity=0 if constant *)
    ; eqs : (term * term) list (* equations / rewrite rules *)
    }

  let print t =
    let { set; ops; eqs } = t in
    let () =match set with
    | None -> print_endline "set is not set"
    | Some s -> Printf.printf "set is %s\n" s in
    Printf.printf "ops len = %d, eqs len = %d\n" (List.length ops) (List.length eqs)

  let check_set t s =
    match t with
    | None -> ()
    | Some s' ->
        if not (s = s') then
          failwith (Printf.sprintf "Inconsistent set: %s vs %s" s s')
        else
          ()

  (** [of_fixpoint_constr] returns t from [Fixpoint ...].
      Currently [Fixpoint ... := match ... with ...] is supported.
      Example of acceptable term:
        Fixpoint plus (n m : G) : G :=
          match n with
          | O => m
          | S p => S (plus p m)
          end.
        *)
  let of_fixpoint_constr env sigma (acc : t) (t : Constr.t) : t =
    if not (Constr.isFix t) then failwith "Not supported form of constant" else
    let (_, (names, types, constrs)) = Constr.destFix t in

    if (Array.length names > 1) || (Array.length types > 1) || (Array.length constrs > 1) then
      failwith "Fixpoint: more than 1 names/types/constrs are not supported"
    else
    let name = Context.binder_name names.(0) in
    let constr = constrs.(0) in
    let rec pick_variables acc (constr : Constr.t) = match Constr.kind constr with
    | Lambda (name, types, constr) -> pick_variables ((Context.binder_name name) :: acc) constr
    | e -> (acc, e) in
    let (vars, e) = pick_variables [] constr in


    if not (Constr.isCase (Constr.of_kind e)) then failwith "Not supported form: match is not used toplevel in Fixpoint" else
    let (ci,univs,_,(nr, _),_,c,arr) = Constr.destCase (Constr.of_kind e) in

    (* c is in [match c with ...]*)
    if not (Constr.isRel c) then
      failwith "Not supported form: In [match c with ...], c should be a variable" else
    let c = Constr.destRel c in
    Printf.printf "c: %d\n" c;
    let matched_pos = List.length vars - c in (* 0-indexed *)

    let ind = ci.ci_ind in
    let (mutind, _) = ind in
    let prefix = Names.MutInd.to_string mutind |> String.split_on_char '.' |> List.rev |> List.tl |> List.rev |> String.concat "." in
    let cases = ComInductive.make_cases ind in
    let cases = List.map (fun case -> (prefix ^ "." ^ (List.hd case)) :: List.tl case) cases in
    let construct_labels = List.map List.hd cases in
    let branches = Array.to_list arr in

    (* convert localenv to string list *)
    let localenv = List.map (fun name -> Pp.string_of_ppcmds (Names.Name.print name)) vars in
    let name_str = name |> Names.Name.print |> Pp.string_of_ppcmds in
    let name_str = prefix ^ "." ^ name_str in
    let localenv = localenv @ [name_str] in (* To reconstruct from rel. Environ may be suitable. *)
    let acc = { acc with ops = (name_str, 0) :: acc.ops } in

    (* Example: In (Fixpoint add n m => match n with ...), gen_lhs (Var "x") returns add (Var "x") m *)
    let gen_lhs (t : term) : term = 
      let f = name_str in
      let vars = List.map (fun name -> name |> Names.Name.print |> Pp.string_of_ppcmds |> mkVar) (List.rev vars) in
      let args = List.mapi (fun i v -> if i = matched_pos then t else v) vars in
      mkTermApp f args in

    let rec aux (acc : t) (branches : Constr.t Constr.pcase_branch list) (cases : string list list) = match branches, cases with
    | [], [] -> acc
    | b :: bs, c :: cs -> begin
        let f = List.hd c in
        let lhs = My_term.mkTermApp f (List.map mkVar (List.tl c)) |> gen_lhs in
        let localenv = List.fold_left (fun acc name -> name :: acc) localenv (List.tl c)  in
        let _ = localenv in
        let rec parse_term (t : Constr.t) : term = match Constr.kind t with
        | Rel i -> mkVar (List.nth localenv (i - 1)) (* Rel is 1-indexed *)
        | App (f, args) ->
          let f = begin match parse_term f with
          | App (f, args) -> failwith "Not supported form: nested App"
          | Var s -> s
          end in
          mkTermApp f (List.map parse_term (Array.to_list args))
        | Construct (construct, instance) ->
          (* NOTE Construct should be all the same *)
          let _, pos = construct in
          let v = List.nth construct_labels (pos - 1) in
          mkVar v
        | Const (k, _) ->
          Printf.printf "Const: %s\n" (Names.Constant.to_string k);
          mkVar (Names.Constant.to_string k)
        | e -> failwith (Printf.sprintf "Not supported form: %s" (label_of_constr e)) in
        let _, rhs = b in
        let rhs = parse_term rhs in
        let eq = (lhs, rhs) in
        Printf.printf "parsed: %s\n" (My_term.to_trs eq);
        Printf.printf "len eqs: %d\n" (List.length acc.eqs);
        let acc = { acc with eqs = eq :: acc.eqs } in
        Printf.printf "len eqs: %d\n" (List.length acc.eqs);
        aux acc bs cs
      end
    | _ -> failwith "Not supported form: number of branches is not equal to number of cases" in
    aux acc branches cases

  let of_econstr env sigma acc (t : Evd.econstr) : t =
    let rec aux acc t : t =
      let open Constr in
      let open EConstr in
      match EConstr.kind sigma t with
      | Construct (constructor, instance) ->
          let (ind, pos) = constructor in
          let (mutind, mutindpos) = ind in
          let set = Names.Label.to_string (Names.MutInd.label mutind) in
          check_set acc.set set;
          let cases = ComInductive.make_cases ind in
          let acc = List.fold_left (fun acc l ->
            let f = List.hd l in
            (* add prefix *)
            let f = ((Names.MutInd.to_string mutind)
              |> String.split_on_char '.' |> List.rev
              |> List.tl |> List.rev |> String.concat ".") ^ "." ^ f in
            let arity = List.length (List.tl l) in
            { acc with ops = (f, arity) :: acc.ops }) acc cases in
          { acc with set = Some set }
      | App (f, arg_arr) -> begin
          if isConst sigma f then (
            let (constant, einstance) = destConst sigma f in
            let acc = Array.fold_left aux acc arg_arr in

            (* lookup def *)
            let constant_body = Environ.lookup_constant constant env in
            let acc = (match constant_body.const_body with
            | Def constr -> begin
                let acc = of_fixpoint_constr env sigma acc constr in
                Feedback.msg_notice Pp.(str "Def " ++ Printer.pr_constr_env env sigma constr);
                acc
              end
            | _ -> failwith "App: Function is not defined yet, which is not supported.") in

            Feedback.msg_notice Pp.(Names.Constant.print constant ++ str ", args: len " ++ int (Array.length arg_arr)
            );
            acc)
          else if isConstruct sigma f then (* Application of Constructor *)
            let (constructor, einstance) = destConstruct sigma f in
            let (ind, pos) = constructor in
            let (mutind, mutindpos) = ind in
            let set = Names.Label.to_string (Names.MutInd.label mutind) in
            check_set acc.set set;
            let cases = ComInductive.make_cases ind in
            let acc = List.fold_left (fun acc l ->
              let f = List.hd l in
              (* add prefix *)
              let f = ((Names.MutInd.to_string mutind)
                |> String.split_on_char '.' |> List.rev
                |> List.tl |> List.rev |> String.concat ".") ^ "." ^ f in
              let arity = List.length (List.tl l) in
              { acc with ops = (f, arity) :: acc.ops }) acc cases in
            { acc with set = Some set }
          else 
            failwith
              (Printf.sprintf "App: Function=%s is neather Const nor Construct, which is not supported."
                              (label_of_constr (EConstr.kind sigma f)))
        end
      | Var id -> acc (* Nothing to do *)
      | t -> failwith ("Not implemented: " ^ label_of_constr t) in
    aux acc t

  let of_goal_concl env sigma (goal_concl : Evd.econstr) : t =
    let open Constr in
    let open EConstr in
    let fail () = failwith "Current goal does not have form \"_ = _\", which is not currently supported." in
    if not (isApp sigma goal_concl) then
      fail ()
    else (* App *)
      let (f, arg_arr) = destApp sigma goal_concl in
      (* This should be _ = _ *)
      if not (isInd sigma f) then fail () else
      let ((mutind, _), _) = destInd sigma f in
      if not ("Coq.Init.Logic.eq" = Names.MutInd.to_string mutind) then
        failwith "Current goal does not have form \"_ = _\" (\"=\" is Coq.Init.Logic.eq), which is not currently supported."
      else
      if not (Array.length arg_arr = 3) then fail () else
      let set = EConstr.kind sigma arg_arr.(0) in
      let l = arg_arr.(1) in
      let r = arg_arr.(2) in
      match set, l, r with
      | Ind ((mutind, _), _), l, r ->
          let set = Names.Label.to_string (Names.MutInd.label mutind) in
          let t = { set=Some set; ops=[]; eqs=[] } in
          let t = of_econstr env sigma t l in
          let t = of_econstr env sigma t r in
          t
      | t, _, _ -> fail ()
end

let rec eq_term_of_my_term (prefix : string option) (t : term) : Equation.Term.t =
  let prefix = match prefix with None -> "" | Some s -> s in
  let add_prefix s = prefix ^ s in
  match t with
  | Var s -> Equation.Term.mkVar (add_prefix s)
  | App (f, args) -> Equation.Term.mkApp (add_prefix f) (List.map (eq_term_of_my_term (Some prefix)) args)

let complete (axioms : Equation.t list) (constants : string list) hint_db_name =
  (* path を付加する (例: "e" => "AutoEqProver.Test.e") *)
  (* let ops =
    List.map
      (fun op ->
        op |> Nametab.global |> Names.GlobRef.print |> Pp.string_of_ppcmds)
      ops
  in *)
  let outputs = Toma.toma_eqs axioms in
  let procedure = Tomaparser.parse outputs in
  let procedure = Tomaparser.add_prefix procedure ("_" ^ hint_db_name ^ "_") in
  let constantsopt : constants option = Some (My_term.constants_of_list constants) in
  let _ = (procedure, constantsopt) in
  (* let outputs = proof_using_toma procedure constantsopt rs hint_db_name in *)
  Pp.str @@ String.concat "\n" outputs

let axiom_ind = Summary.ref ~name:"axiom_ind" 0
let get_unique_axiom_name () =
  let n = !axiom_ind in
  axiom_ind := n + 1;
  Printf.sprintf "axiom%d" n


let debug_add_single_axiom () =
  let eq = Equation.create ~varnames:["m"]
    ~left:Equation.Term.(mkApp "plus" [mkVar "O"; mkVar "m"])
    ~right:Equation.Term.(mkVar "m") in
  let t = Equation.to_constr_expr eq in
  let name = Names.Id.of_string (get_unique_axiom_name ()) in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, body = Constrintern.interp_constr_evars env sigma t in
  let typ = EConstr.to_constr sigma body in
  let info = Declare.Info.make ~poly:false () in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  let t, types, uctx, obl_info =
    Declare.Obls.prepare_obligation ~name ~types:None ~body sigma
  in
  let tactic =
    let open Proofview.Notations in
    Tactics.intros <*>
    Tactics.simpl_in_concl <*>
    Tactics.reflexivity in
  let _, progress =
    Declare.Obls.add_definition ~pm:Declare.OblState.empty ~cinfo ~info ~uctx
      ~tactic obl_info
  in
  let () = match progress with
  | Defined _ -> Printf.printf "Defined %s\n" (Names.Id.to_string name)
  | _ -> failwith ("Could not prove axiom: " ^ Names.Id.to_string name) in
  Proofview.tclUNIT ()

let get_rules_from_hyps sigma (hyps : EConstr.named_context) : Equation.t list =
  List.filter_map (function
  | Context.Named.Declaration.LocalDef _ ->
    Feedback.msg_warning (Pp.str "cople_auto: LocalDef is ignored (not implemented)");
    None
  | Context.Named.Declaration.LocalAssum (annot, types) ->
    let name = Context.binder_name annot |> Names.Id.to_string in
    Printf.printf "HYP: assum (%s)\n" name;
    if name = "IHn" then
      (* FIXME: currently only IHn is supported *)
      let eq = Equation.of_constr (EConstr.to_constr sigma types) in
      Printf.printf "IHn: %s\n" (Equation.to_trs_string eq);
      Some eq
    else
      None
  ) hyps

let get_constants_from_hyps sigma (hyps : EConstr.named_context) (set : string) : string list =
  List.filter_map (function
  | Context.Named.Declaration.LocalDef _ ->
    Feedback.msg_warning (Pp.str "cople_auto: LocalDef is ignored (not implemented)");
    None
  | Context.Named.Declaration.LocalAssum (annot, types) ->
    let name = Context.binder_name annot |> Names.Id.to_string in
    let is_constant = match EConstr.kind sigma types with
    | Constr.Ind (inductive, instance) ->
      set = Names.Label.to_string (Names.MutInd.label (fst inductive))
    | _ -> (
      let warn = Printf.sprintf "get_constants_from_hyps: ignore kind: %s\n" (label_of_constr (EConstr.kind sigma types)) in
      Feedback.msg_warning (Pp.str warn);
      false) in
    if is_constant then
      Some name
    else
      None
  ) hyps

let get_constant_body gref =
  let open Names.GlobRef in
  match gref with
  | ConstRef cst ->
      let cb = Global.lookup_constant cst in
      cb
  | _ -> failwith "Invalid input"

let const_body_of_constant_qualid (ln : Libnames.qualid) : Constr.t =
  let gref = Nametab.global ln in
  let cb = get_constant_body gref in
  match cb.const_body with
  | Def c -> c
  | _ -> failwith "const_body_of_constant_qualid: not Def"

let compl_auto (fixpoints : string list) =
  Proofview.Goal.enter (fun gl ->
    let (concl, env, sigma, hyps) = Proofview.Goal.(concl gl, env gl, sigma gl, hyps gl) in
    let input = CompletionInput.of_goal_concl env sigma concl in
    let input = List.fold_left (fun acc fixpoint ->
      let constr = const_body_of_constant_qualid (Libnames.qualid_of_string fixpoint) in
      CompletionInput.of_fixpoint_constr env sigma acc constr) input fixpoints in
    (* debug *)
    let ({ set; ops; eqs }: CompletionInput.t) = input in
    match set with
    | None -> failwith "set is not set"
    | Some s -> Printf.printf "set is %s\n" s;
    Printf.printf "eqs:\n";
    List.iter (fun eq -> Printf.printf "%s\n" (My_term.to_trs eq)) eqs;
    Printf.printf "eqs end:\n";

    let setname = match set with None -> "G" | Some s -> s in
    let cs = get_constants_from_hyps sigma hyps setname in
    Printf.printf "constants:\n";
    List.iter (fun c -> Printf.printf "%s\n" c) cs;
    let ops = List.map fst ops |> List.sort_uniq (String.compare) in
    let ops = cs @ ops in
    let ops = List.sort_uniq (String.compare) ops in

    Printf.printf "ops len = %d, eqs len = %d\n" (List.length ops) (List.length eqs);
    List.iter (fun op -> Printf.printf "op: %s\n" op) ops;

    let constants = ops in
    let eqs = List.map (fun (left, right) ->
      (* let prefix = Some "e2e_tests.NatInd." in *)
      let prefix = Some "" in (* TODO: Fixme *)
      let left = eq_term_of_my_term prefix left in
      let right = eq_term_of_my_term prefix right in
      Equation.create_with_constants ~constants ~left ~right) eqs in
    let eqs_of_hyps = get_rules_from_hyps sigma hyps in
    let eqs = eqs_of_hyps @ eqs in

    Feedback.msg_notice (Printer.pr_econstr_env env sigma concl);

    Feedback.msg_notice (complete eqs ops "hint_db_name");

    let outputs = Toma.toma_eqs eqs in
    let procedure = Tomaparser.parse outputs in
    let (proofs, rules, _) = procedure in

    (* assert *)
    match List.find_opt (fun (_, s) -> match s with Tomaparser.Axiom -> false | _ -> true) proofs with
    | Some _ -> failwith "currently proofs should be all Axiom"
    | None ->

    let open Proofview.Notations in
    let tactic prf =
      let (rule, _) = prf in
      let constants = My_term.constants_of_list constants in
      let t = (fst (snd rule), snd (snd rule)) in
      Printf.printf "t: %s\n" (My_term.to_trs t);
      let goal =
        My_term.to_constrexpr_raw t constants
      in
      let sigma, goal = Constrintern.interp_constr_evars env sigma goal in
      let tcl1 =
       (Tactics.simpl_in_concl
       <*> Tactics.reflexivity) in
      let tcl2 = Auto.default_full_auto in
      Tactics.assert_by
      (Names.Name.mk_name (Names.Id.of_string ("axiom" ^ (fst rule)))) (* TODO: name *)
      goal
      @@ Proofview.tclIFCATCH tcl2
        (fun () -> Printf.printf "Defined\n"; Proofview.tclUNIT ())
        (fun (e, _) -> Printf.printf "Err: %s\n" (Printexc.to_string e); Feedback.msg_notice Pp.(str "ERRR"); tcl1) in
    
    let tcl = List.fold_left (fun acc prf -> acc <*> tactic prf) (Proofview.tclUNIT ()) (List.rev proofs) in

    let open Tactypes in
    (* let open Rewrite in *)
    (*
    let rewriteLR c at = cl_rewrite_clause c true (OnlyOccurrences [ at ]) None in *)
    let open Equality in
    let rewriteLR_with_binds c =
      let binds = NoBindings in
      general_rewrite ~where:None ~l2r:true (OnlyOccurrences [ 1 ]) ~freeze:true
        ~dep:true ~with_evars:false (c, binds)
    in

    let tclAUTO_REWRITE =
      let tcl = List.fold_left (fun acc (rule, _) ->
        let id = fst rule in
        let rewriter = ("axiom" ^ id) in
        (* let _ = cl_rewrite_clause_innermost rewriter true in *)
        let tac = rewriteLR_with_binds (EConstr.mkVar (Names.Id.of_string rewriter)) in
        Proofview.tclIFCATCH tac (fun () -> print_endline "ok"; Proofview.tclUNIT ()) (fun (e, _) -> Printf.printf "FAIL: %s\n" (Printexc.to_string e); acc))
        (Proofview.tclUNIT ()) proofs in
      let rec tclLOOP () =
        Proofview.tclIFCATCH
          (Tacticals.tclPROGRESS tcl)
          (fun () -> print_endline "prog"; tclLOOP ())
          (fun _ -> print_endline "fin"; Proofview.tclUNIT ()) in
      tclLOOP () in

    tcl <*> tclAUTO_REWRITE <*> Tactics.reflexivity
    )
