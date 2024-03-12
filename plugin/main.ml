open Constrexpr
open My_term
open Tomaparser
open Autorewrite
open Rewrite

(** 公理のうちのどれかから直ちに導ける規則を証明する
    公理の一つと同じか、両辺を入れ替えたものである必要がある。*)
let prove_by_axiom ~name ~goal ~axioms =
  let tactic_of axiom use_symmetry =
    let open Proofview.Notations in
    Tactics.intros <*>
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
    | [], _ -> failwith ("Could not prove axiom: " ^ (Names.Id.to_string name))
    | hd :: tl, _ ->
      let tactic = tactic_of hd use_symmetry in
      let tactic = Proofview.tclORELSE tactic (fun _ -> Tacticals.tclIDTAC) in
      let _, progress = Declare.Obls.add_definition ~pm:(Declare.OblState.empty) ~cinfo ~info ~uctx ~tactic obl_info in
      begin match progress with
      | Defined _ -> ()
      | _ ->
        if use_symmetry then try_proof tl false
        else try_proof axioms true
      end in
  try_proof axioms false

let add_axiom (rule : rule) (constants : constants option) axioms =
  let name = Names.Id.of_string ("t" ^ fst rule) in
  let constants = (match constants with None -> My_term.default_constants | Some cs -> cs) in
  let goal = My_term.to_constrexpr_raw (fst (snd rule), snd (snd rule)) constants in
  let () = prove_by_axiom ~name ~goal ~axioms in
  ()

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
  let evars = My_term.variables_except_constants (l, r) constants in
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
  let explicit_bind v =
    if List.mem v evars then
      CAst.make (NamedHyp (CAst.make (Names.Id.of_string v)), (EConstr.mkVar (Names.Id.of_string v)))
    else
      (*
        Goal に含まれない変数の場合、rewriteタクティクのbind変数として使用すると Unbound のエラーが生じてしまう。
        Goal:A=C を ２つのB=A, B=Cで示す際に、Bのみに含まれる変数がある状況が該当する。
        このような状況で生じる変数は式変換の一部で現れ、結果に含まれないため、どの変数/定数でも良い。
        よって、定数とGoalの変数のうち一つを採用する。
      *)
      let binder = List.hd (evars @ (My_term.list_of_constants constants)) in
      CAst.make (NamedHyp (CAst.make (Names.Id.of_string v)), (EConstr.mkVar (Names.Id.of_string binder)))
  in
  let rewriteLR_with_binds c (vars : string list) =
    let binds = ExplicitBindings (List.map explicit_bind vars) in
    general_rewrite ~where:None ~l2r:true (OnlyOccurrences [1]) ~freeze:true ~dep:true ~with_evars:false (c, binds) in
  let rewriteRL_with_binds c (vars : string list) =
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
    let tactic = Proofview.tclORELSE tactic (fun _ -> Tacticals.tclIDTAC) in
    let _, progress = Declare.Obls.add_definition ~pm:(Declare.OblState.empty) ~cinfo ~info ~uctx:ustate ~tactic obl_info in
    begin match progress with
    | Remain _ -> try_proof (next_pair (at1, at2))
    | Dependent -> try_proof (next_pair (at1, at2))
    | Defined _ -> ()
    end
    in
  let () = try_proof (1, 1) in
    Pp.strbrk "Proof"

let cl_rewrite_clause_innermost ?(hyp:string = "H") (rewriter:Libnames.qualid) (left2right:bool) =
  let open Rewrite in
  let c_delayed = fun env sigma -> sigma, ((EConstr.mkRef (Nametab.global rewriter, EConstr.EInstance.empty))) in
  let strat_ast = StratUnary (Innermost, StratConstr ((DAst.make (Glob_term.GVar (Names.Id.of_string "temp")), c_delayed), left2right)) in
  let strat = strategy_of_ast strat_ast in
  cl_rewrite_clause_strat strat (Some (Names.Id.of_string hyp))

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
  (*
    項の左右方向に関わらず証明するため、N個の書き換え規則に対して、l2rs として N+1 個のboolの組み合わせを受け取る。
    l2rs[0]  : symmetry. を使用するかどうか
    l2rs[1:] : i個目の cl_rewrite_clause の書き換え方向を -> にするかどうかを l2rs[i] で表す。
    term の形を調べるかtomaの出力を修正すれば事前に書き換え方向は決定できそうだが、実装の簡単のため全ての組み合わせを試す。
   *)
  let gen_tactic l2rs =
    let use_symmetry = List.hd l2rs in
    let l2rs = List.tl l2rs in
    Tactics.intros <*>
    Tactics.pose_proof (Names.Name (Names.Id.of_string "H")) (EConstr.mkRef (Nametab.global applier, EConstr.EInstance.empty)) <*>
    List.fold_left (fun prev cur -> prev <*> cur) Tacticals.tclIDTAC (
      List.map (fun (rewriter, l2r) -> 
        cl_rewrite_clause_innermost rewriter l2r
        ) (List.combine rewriters l2rs)) <*>
    (if use_symmetry then Tactics.symmetry else Tacticals.tclIDTAC) <*>
    Auto.default_auto in
  let rec try_proof l2rs =
    let tactic = gen_tactic l2rs in
    let tactic = Proofview.tclORELSE tactic (fun _ -> Tacticals.tclIDTAC) in
    let _, progress = Declare.Obls.add_definition ~pm:(Declare.OblState.empty) ~cinfo ~info ~uctx:ustate ~tactic obl_info in
    match progress with
    | Defined _ -> ()
    | _ ->
      begin match Devutil.next_binls l2rs with
      | None -> failwith ("Could not prove simp: " ^ (Names.Id.to_string name))
      | Some l2rs -> try_proof l2rs
      end in
  try_proof (List.init (List.length rewriters + 1) (fun _ -> true))

let add_rules_for_termination (rules : rule list) =
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

let proof_using_toma (proc : procedure) (constants : constants option) axioms : string list =
  let open Tomaparser in
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
  List.iteri (fun i p -> print_endline ("PROVING t" ^ (fst (fst p))); prove p) proofs; 
  add_rules_for_termination (snd proc);
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
  let outputs = Toma.toma axioms in
  List.iter print_endline outputs;
  let procedure = Tomaparser.parse outputs in
  let constantsopt: constants option = Some (My_term.constants_of_list ops) in
  let outputs = proof_using_toma procedure constantsopt rs in
  Pp.str @@ String.concat "\n" outputs
