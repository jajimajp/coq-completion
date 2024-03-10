open Constrexpr
open My_term
open Tomaparser
open Autorewrite
open Rewrite

module SS = Set.Make(String)

(** 公理のうちのどれかから直ちに導ける規則を証明する
    公理の一つと同じか、両辺を入れ替えたものである必要がある。*)
let prove_by_axiom ~name ~goal ~axioms =
  let tactic_of axiom use_symmetry =
    let open Proofview.Notations in
    (if use_symmetry then Tactics.symmetry else Tacticals.tclIDTAC) <*>
    Tactics.apply (EConstr.mkRef (Nametab.global axiom, EConstr.EInstance.empty)) in
  let env = Global.env () in 
  let sigma = Evd.from_env env in
  let (sigma, body) = Constrintern.interp_constr_evars env sigma goal in
  let typ = EConstr.to_constr sigma body in
  let info = Declare.Info.make ~poly:false () in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  let (t, types, uctx, obl_info) = Declare.Obls.prepare_obligation ~name ~types:None ~body sigma in
  let rec try_proof axioms use_symmetry =
    match axioms, use_symmetry with
    | [], _ -> failwith "Could not prove"
    | hd :: tl, _ ->
      let tactic = tactic_of hd use_symmetry in
      let _, progress = Declare.Obls.add_definition ~pm:(Declare.OblState.empty) ~cinfo ~info ~uctx ~tactic obl_info in
      begin match progress with
      | Defined _ -> ()
      | _ ->
        if use_symmetry then try_proof tl false
        else try_proof axioms true
      end in
  try_proof axioms false

(*
  書換規則をヒントDBに追加する

  base ヒントDB名
  lcsr 定理を表す項

  extratactics.mlg を参考に実装
  簡単のため、"->" のみで、"using"は使わず、local で宣言するようにしている
*)
let add_local_rewrite_hint (base: string) (lcsr: Constrexpr.constr_expr) : Pp.t =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let f ce =
    let c, ctx = Constrintern.interp_constr env sigma ce in
    let c = EConstr.to_constr sigma c in
    let ctx =
      let ctx = UState.context_set ctx in
        (DeclareUctx.declare_universe_context ~poly:false ctx;
          Univ.ContextSet.empty)
    in
      CAst.make ?loc:(Constrexpr_ops.constr_loc ce) ((c, ctx), (* ort *) true, (* t *) None) in
  let eq = f lcsr in
  let add_hints base = add_rew_rules ~locality:Local base [eq] in
  let _ = add_hints base in
  Pp.strbrk "Added rewrite hints."

let add_axiom (rule : V6.rule) (constants : constants option) axioms =
  let name = Names.Id.of_string ("t" ^ fst rule) in
  let constants = (match constants with None -> My_term.default_constants | Some cs -> cs) in
  let goal = My_term.to_constrexpr_raw (fst (snd rule), snd (snd rule)) constants in
  let () = prove_by_axiom ~name ~goal ~axioms in
  ()

let add_axioms (records : tomarule  list) (proved: SS.t) (constants: constants option) axioms: (string list * SS.t) =
  let rec aux records outputs proved =
    match records with
    | [] -> outputs, proved
    | (id, left, right) :: rest ->
      if SS.mem id proved then
        aux rest (("skip " ^ id) :: outputs) proved
      else
        let name = Names.Id.of_string ("t" ^ id) in
        let constants = (match constants with None -> My_term.default_constants | Some cs -> cs) in
        let goal = My_term.to_constrexpr_raw (left, right) constants in
        let () = prove_by_axiom ~name ~goal ~axioms in
        let proved = SS.add id proved in
          aux rest (("proved(by axiom) t" ^ id) :: outputs) proved
    in
    let outputs, proved = aux records [] proved in
    List.rev outputs, proved

(*
  critical_pair による定理の証明
  name: 定理の名前
  n1: 証明に使う１つ目の定理名
  n2: 証明に使う２つ目の定理名
  l: 定理の左辺
  r: 定理の右辺
  crit: critical pair
*)
let proof_using_crit ~name ~n1 ~n2 ~l ~r ~crit ~(constants:constants option) =
  let constants = begin match constants with
  | None -> My_term.default_constants
  | Some cs -> cs
  end in
  let e = My_term.to_constrexpr_raw (l, r) constants in
  let e1 = My_term.to_constrexpr_raw (crit, l) constants in
  let e1vars = My_term.variables_except_constants (crit, l) constants in
  let e2 = My_term.to_constrexpr_raw (crit, r) constants in
  let e2vars = My_term.variables_except_constants (crit, r) constants in
  let r1 = Libnames.qualid_of_string n1 in
  let r2 = Libnames.qualid_of_string n2 in
  let env = Global.env () in 
  let sigma = Evd.from_env env in
  let (sigma, body) = Constrintern.interp_constr_evars env sigma e in
  let (sigma, e1) = Constrintern.interp_constr_evars env sigma e1 in
  let (sigma, e2) = Constrintern.interp_constr_evars env sigma e2 in
  let typ = EConstr.to_constr sigma body in
  let info = Declare.Info.make ~poly:false () in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  let (t, types, ustate, obl_info) = Declare.Obls.prepare_obligation ~name ~types:None ~body sigma in
  let open Proofview.Notations in
  let open Equality in
  let open Tactypes in
  let rewriteLR c at =
    cl_rewrite_clause c true (OnlyOccurrences [at]) None in
  let rewriteLR_with_binds c (vars : string list) =
    let explicit_bind v = CAst.make (NamedHyp (CAst.make (Names.Id.of_string v)), (EConstr.mkVar (Names.Id.of_string v))) in
    let binds = ExplicitBindings (List.map explicit_bind vars) in
    general_rewrite ~where:None ~l2r:true (OnlyOccurrences [1]) ~freeze:true ~dep:true ~with_evars:false (c, binds) in
  let rewriteRL_with_binds c (vars : string list) =
    let explicit_bind v = CAst.make (NamedHyp (CAst.make (Names.Id.of_string v)), (EConstr.mkVar (Names.Id.of_string v))) in
    let binds = ExplicitBindings (List.map explicit_bind vars) in
    general_rewrite ~where:None ~l2r:false (OnlyOccurrences [1]) ~freeze:true ~dep:true ~with_evars:false (c, binds) in
  let gen_tactic at1 at2 = Tactics.assert_by Names.Name.Anonymous e1 (
      Tactics.intros
      <*> rewriteLR (fun env sigma -> sigma, ((EConstr.mkRef (Nametab.global r1, EConstr.EInstance.empty)), NoBindings)) at1
      <*> Tactics.reflexivity)
    <*> Tactics.assert_by Names.Name.Anonymous e2 (
      Tactics.intros
      <*> rewriteLR (fun env sigma -> sigma, ((EConstr.mkRef (Nametab.global r2, EConstr.EInstance.empty)), NoBindings)) at2
      <*> Tactics.reflexivity)
    <*> Tactics.intros
    <*> rewriteRL_with_binds (EConstr.mkVar (Names.Id.of_string "H")) e1vars
    <*> rewriteLR_with_binds (EConstr.mkVar (Names.Id.of_string "H0")) e2vars
    <*> Tactics.reflexivity in
  let rec try_proof (at1, at2) =
    (* 自然数のペアに対して、次のペアを返す関数。 (1, 1)から始めると全てのペアを列挙する。 *)
    (* 例: (1, 1), (1, 2), (2, 2), (2, 1), (1, 3), ... *)
    let next_pair (x, y) =
      if y = 1 then
        (1, x + 1)
      else if x < y then (* 対角線より左側にある点 *)
        (x + 1, y)
      else 
        (x, y - 1)
    in
    let tactic = gen_tactic at1 at2 in
    let _, progress = Declare.Obls.add_definition ~pm:(Declare.OblState.empty) ~cinfo ~info ~uctx:ustate ~tactic obl_info in
    begin match progress with
    | Remain _ -> try_proof (next_pair (at1, at2))
    | Dependent -> try_proof (next_pair (at1, at2))
    | Defined _ -> ()
    end
    in
  let () = try_proof (1, 1) in
    Pp.strbrk "Proof"

let proof_using_critical_pairs (pairs : (tomarule * termid * termid * term) list) (proved: SS.t) (constants: constants option) =
  let rec aux pairs outputs proved =
    match pairs with
    | [] -> outputs, proved
    | ((id, l, r), n1, n2, crit) :: rest ->
      if SS.mem id proved then
        aux rest (("skip t" ^ id) :: outputs) proved
      else
        let n1 = "t" ^ n1 in
        let n2 = "t" ^ n2 in
        let name = Names.Id.of_string ("t" ^ id) in
        let _ = proof_using_crit ~name ~n1 ~n2 ~l ~r ~crit ~constants in
        let proved = SS.add id proved in
          aux rest (("proved t" ^ id) :: outputs) proved
    in
  let outputs, proved = aux pairs [] proved in
  List.rev outputs, proved

let prove_interreduce
  ~(name:Names.Id.t) (* 証明する定理名 *)
  ~(goal:Constrexpr.constr_expr) (* 定理の型 *)
  ~(rewriters:Libnames.qualid list)
  ~(applier:Libnames.qualid) (* apply を行う定理名 *)
  =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let (sigma, body) = Constrintern.interp_constr_evars env sigma goal in
  let typ = EConstr.to_constr sigma body in
  let info = Declare.Info.make ~poly:false () in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  let (t, types, ustate, obl_info) = Declare.Obls.prepare_obligation ~name ~types:None ~body sigma in
  let open Proofview.Notations in
  let open Tactypes in
  let () = print_endline @@ "app: " ^ (Libnames.string_of_qualid applier) in
  let gen_tactic use_symmetry =
    Tactics.intros <*>
    Tactics.pose_proof (Names.Name (Names.Id.of_string "H")) (EConstr.mkRef (Nametab.global applier, EConstr.EInstance.empty)) <*>
    List.fold_left (fun prev cur -> prev <*> cur) Tacticals.tclIDTAC (
      List.map (fun rewriter -> 
        cl_rewrite_clause (fun env sigma -> sigma, ((EConstr.mkRef (Nametab.global rewriter, EConstr.EInstance.empty)), NoBindings)) true (OnlyOccurrences [1]) (Some (Names.Id.of_string "H"))
        ) rewriters) <*>
    (if use_symmetry then Tactics.symmetry else Tacticals.tclIDTAC) <*>
    Tactics.apply (EConstr.mkVar (Names.Id.of_string "H")) in
  let rec try_proof use_symmetry =
    let tactic = gen_tactic use_symmetry in
    let _, progress = Declare.Obls.add_definition ~pm:(Declare.OblState.empty) ~cinfo ~info ~uctx:ustate ~tactic obl_info in
    let use_symmetry' = if use_symmetry then false else true in
    begin match progress with
    | Remain _ -> if use_symmetry then failwith "Could not prove" else try_proof use_symmetry'
    | Dependent -> if use_symmetry then failwith "Could not prove" else try_proof use_symmetry'
    | Defined _ -> ()
    end in
  try_proof false

let proof_interreduce (records : ((tomarule * tomarule * termid list) list)) (proved: SS.t) (constants: constants option): (string list * SS.t) =
  let rec aux records outputs proved =
    match records with
    | [] -> outputs, proved
    | ((previd, prevl, prevr), (nextid, nextl, nextr), rewriterids) :: rest ->
      if SS.mem nextid proved then
        aux rest (("skip " ^ nextid) :: outputs) proved
      else
        let name = Names.Id.of_string ("t" ^ nextid) in
        let rewriters = List.map (fun id -> Libnames.qualid_of_string ("t" ^ id)) rewriterids in
        let applier = Libnames.qualid_of_string ("t" ^ previd) in
        let constants = (match constants with None -> My_term.default_constants | Some cs -> cs) in
        let goal = My_term.to_constrexpr_raw (nextl, nextr) constants in
        let () = prove_interreduce ~name ~goal ~rewriters ~applier in
        let proved = SS.add nextid proved in
          aux rest (("proved(interreduce) t" ^ nextid) :: outputs) proved
    in
    let outputs, proved = aux records [] proved in
    List.rev outputs, proved

let add_rules_for_termination (rules : tomarule list) =
  let rec aux = function
  | [] -> ()
  | (id, _, _) :: tl ->
      let _ = add_local_rewrite_hint "hint_compl" (CAst.make (
        CRef (
          Libnames.qualid_of_string @@ "t" ^ id,
          None
        )
      )) in
      aux tl
  in aux rules

let add_rules_for_termination_v6 (rules : V6.rule list) =
  let rec aux = function
  | [] -> ()
  | (id, (_, _)) :: tl ->
      let _ = add_local_rewrite_hint "hint_compl" (CAst.make (
        CRef (
          Libnames.qualid_of_string @@ "t" ^ id,
          None
        )
      )) in
      aux tl
  in aux rules

let proof_using_toma (sections : Tomaparser.tomaoutputsection list) (constants: constants option) axioms : string list =
  let open Tomaparser in
  let rec aux sections outputs proved dbg_cnt =
    if dbg_cnt = 30 then outputs else (* DEBUG *)
    match sections with
    | [] -> outputs
    | section :: rest -> begin
      match section with
      | Axioms rules ->
        let (outputs', proved) = add_axioms rules proved constants axioms in
        aux rest (outputs @ outputs') proved (dbg_cnt + 1)
      | ReductionOrder rules ->
        (* 現状、reductionorder: に対する新たな規則の証明は起こらない *)
        aux rest outputs proved (dbg_cnt + 1)
      | CriticalPairs pairs ->
        let (outputs', proved) = proof_using_critical_pairs pairs proved constants in
        aux rest (outputs @ outputs') proved (dbg_cnt + 1)
      | Interreduce records ->
        let (outputs', proved) = proof_interreduce records proved constants in
        aux rest (outputs @ outputs') proved (dbg_cnt + 1)
      | TerminationSuccess rules ->
        let () = add_rules_for_termination rules in
        outputs
    end in
  List.rev (aux sections [] (SS.empty) 0)

let proof_using_toma_v6 (proc : V6.procedure) (constants : constants option) axioms : string list =
  let open Tomaparser in
  let open V6 in
  let proofs = fst proc in
  let prove (rule, strat) = match strat with
  | Axiom ->
    add_axiom rule constants axioms
  | Crit (r1, r2, crit) ->
    let n1 = "t" ^ (fst r1) in
    let n2 = "t" ^ (fst r2) in
    ignore @@ proof_using_crit ~name:(Names.Id.of_string ("t" ^ fst rule)) ~n1 ~n2 ~l:(fst (snd rule)) ~r:(snd (snd rule)) ~crit ~constants
  | Simp (prev, rewriters) ->
    let constants = (match constants with None -> My_term.default_constants | Some cs -> cs) in
    ignore @@ prove_interreduce ~name:(Names.Id.of_string ("t" ^ (fst rule)))
                                ~goal:(My_term.to_constrexpr_raw (snd rule) constants)
                                ~rewriters:(List.map (fun id -> Libnames.qualid_of_string ("t" ^ id)) rewriters)
                                ~applier:(Libnames.qualid_of_string ("t" ^ (fst prev))) in
  let rec take ls n =
    match ls, n with
    | _, 0 -> []
    | [], _ -> []
    | hd :: tl, _ -> hd :: take tl (n - 1) in
  List.iter prove (take proofs 60); 
  add_rules_for_termination_v6 (snd proc);
  []

let get_constant_body gref =
  let open Names.GlobRef in
  match gref with
  | ConstRef cst ->
    let cb = Global.lookup_constant cst in
    cb
  | _ -> failwith "Invalid input"

let constr_of_qualid (ln: Libnames.qualid): Constr.t =
  let gref = Nametab.global ln in
  let cb = get_constant_body gref in
  cb.const_type

let complete rs dbName ops =
  let axioms = List.map constr_of_qualid rs in
  (* path を付加する (例: "e" => "AutoEqProver.Test.e") *)
  let ops = List.map (fun op ->
    op |> Nametab.global |> Names.GlobRef.print |> Pp.string_of_ppcmds) ops in
  let outputs = Toma.V6.toma axioms in
  (* DEBUG *)
  List.iter print_endline outputs;
  let procedure = Tomaparser.V6.parse outputs in
  let constantsopt: constants option = Some (My_term.constants_of_list ops) in
  let outputs = proof_using_toma_v6 procedure constantsopt rs in
  Pp.str @@ String.concat "\n" outputs
