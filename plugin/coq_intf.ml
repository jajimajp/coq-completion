open Rewrite
open Tomaparser

let cl_rewrite_clause_innermost ?(hyp:string = "H") (rewriter:Libnames.qualid) (left2right:bool) =
  let open Rewrite in
  let c_delayed = fun env sigma -> sigma, ((EConstr.mkRef (Nametab.global rewriter, EConstr.EInstance.empty))) in
  let strat_ast = StratUnary (Innermost, StratConstr ((DAst.make (Glob_term.GVar (Names.Id.of_string "temp")), c_delayed), left2right)) in
  let strat = strategy_of_ast strat_ast in
  cl_rewrite_clause_strat strat (Some (Names.Id.of_string hyp))


(** 現在のゴールを、公理のうちいずれか一つを使って示す。
    ゴールは公理と等しいか、両辺を入れ替えたものである必要がある。*)
let tac_prove_by_axiom ~(axioms : Libnames.qualid list) =
  let open Proofview.Notations in
  let tactic_of axiom use_symmetry =
    Tactics.intros <*>
    (if use_symmetry then Tactics.symmetry else Tacticals.tclIDTAC) <*>
    Tactics.apply (EConstr.mkRef (Nametab.global axiom, EConstr.EInstance.empty))
  in
  let rec aux axioms use_symmetry =
    match axioms with
    | [] -> Tacticals.tclFAIL (Pp.str "Could not prove goal by axioms.")
    | hd :: tl ->
      Tacticals.tclIFCATCH
        (Tacticals.tclPROGRESS (tactic_of hd use_symmetry))
        (fun _ -> Tacticals.tclIDTAC)
        (fun _ ->
          match use_symmetry with
          | false ->
            aux axioms true
          | true ->
            aux tl false) in
  aux axioms false

let prove_by_axiom ~name ~goal ~axioms =
  let env = Global.env () in 
  let sigma = Evd.from_env env in
  let (sigma, body) = Constrintern.interp_constr_evars env sigma goal in
  let typ = EConstr.to_constr sigma body in
  let info = Declare.Info.make ~poly:false () in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  let (t, types, uctx, obl_info) = Declare.Obls.prepare_obligation ~name ~types:None ~body sigma in
  let tactic = tac_prove_by_axiom ~axioms in
  let _, progress = Declare.Obls.add_definition ~pm:(Declare.OblState.empty) ~cinfo ~info ~uctx ~tactic obl_info in
  match progress with
  | Defined _ -> ()
  | _ -> failwith ("Could not prove axiom: " ^ (Names.Id.to_string name))

let tac_single_prove_by_crit ~evars ~constants ~e1 ~e2 ~r1 ~r2 ~crit ~l ~r at1 at2 =
  let e1vars = My_term.variables_except_constants (crit, l) constants in
  let e2vars = My_term.variables_except_constants (crit, r) constants in
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
  let _ = (* prevent warn *)
    let _ = rewriteLR (fun env sigma -> sigma, ((EConstr.mkRef (Nametab.global r1, EConstr.EInstance.empty)), NoBindings)) 1 in
    let _ = rewriteLR_with_binds (EConstr.mkVar (Names.Id.of_string "H")) e1vars in
    let _ = rewriteRL_with_binds (EConstr.mkVar (Names.Id.of_string "H")) e2vars in () in
  let tactic_of at1 at2 =
      Tactics.assert_by (Names.Name.mk_name (Names.Id.of_string "H_0")) e1 (
        Tactics.intros
        <*> rewriteLR (fun env sigma -> sigma, ((EConstr.mkRef (Nametab.global r1, EConstr.EInstance.empty)), NoBindings)) at1
        <*> Tactics.reflexivity)
      <*> Tactics.assert_by (Names.Name.mk_name (Names.Id.of_string "H_1")) e2 (
        Tactics.intros
        <*> rewriteLR (fun env sigma -> sigma, ((EConstr.mkRef (Nametab.global r2, EConstr.EInstance.empty)), NoBindings)) at2
        <*> Tactics.reflexivity)
      <*> Tactics.intros
      <*> rewriteRL_with_binds (EConstr.mkVar (Names.Id.of_string "H_0")) e1vars
      <*> rewriteLR_with_binds (EConstr.mkVar (Names.Id.of_string "H_1")) e2vars
      <*> Tactics.reflexivity
  in tactic_of at1 at2

let tac_prove_by_crit ~evars ~constants ~e1 ~e2 ~r1 ~r2 ~crit ~l ~r =
  let e1vars = My_term.variables_except_constants (crit, l) constants in
  let e2vars = My_term.variables_except_constants (crit, r) constants in
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
  let _ = (* prevent warn *)
    let _ = rewriteLR (fun env sigma -> sigma, ((EConstr.mkRef (Nametab.global r1, EConstr.EInstance.empty)), NoBindings)) 1 in
    let _ = rewriteLR_with_binds (EConstr.mkVar (Names.Id.of_string "H")) e1vars in
    let _ = rewriteRL_with_binds (EConstr.mkVar (Names.Id.of_string "H")) e2vars in () in
  let tactic_of at1 at2 =
      (* Tactics.assert_by Names.Name.Anonymous e1 (
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
      <*> Tactics.reflexivity  *)


      Tactics.assert_by (Names.Name.mk_name (Names.Id.of_string "H_0")) e1 (
        Tactics.intros
        <*> rewriteLR (fun env sigma -> sigma, ((EConstr.mkRef (Nametab.global r1, EConstr.EInstance.empty)), NoBindings)) at1
        <*> Tactics.reflexivity)
      <*> Tactics.assert_by (Names.Name.mk_name (Names.Id.of_string "H_1")) e2 (
        Tactics.intros
        <*> rewriteLR (fun env sigma -> sigma, ((EConstr.mkRef (Nametab.global r2, EConstr.EInstance.empty)), NoBindings)) at2
        <*> Tactics.reflexivity)
      <*> Tactics.intros
      <*> rewriteRL_with_binds (EConstr.mkVar (Names.Id.of_string "H_0")) e1vars
      <*> rewriteLR_with_binds (EConstr.mkVar (Names.Id.of_string "H_1")) e2vars
      <*> Tactics.reflexivity
      (* <*> Tacticals.tclIDTAC *)
  in
  (* 自然数のペアに対して、次のペアを返す関数。 (1, 1)から始めると全てのペアを列挙する。 *)
  (* 例: (1, 1), (1, 2), (2, 2), (2, 1), (1, 3), ... *)
  let next_pair (x, y) =
    (* fail *) if x = 3 then failwith "fail: Too many pairs."
    else
    if y = 1 then
      (1, x + 1)
    else if x < y then (* 対角線より左側にある点 *)
      (x + 1, y)
    else 
      (x, y - 1) in
  let rec aux (at1, at2) =
  (* let aux (at1, at2) = *)
    (* (tactic_of at1 at2) in *)
    Tacticals.tclIFCATCH
      (try Tacticals.tclPROGRESS (tactic_of at1 at2) with exn -> print_endline ("xn: " ^ Printexc.to_string exn); Tacticals.tclFAIL (Pp.str "fl"))
      (fun _ -> Tacticals.tclIDTAC)
      (fun _ -> aux (next_pair (at1, at2))) in
  aux (1, 1)


(*
  critical_pair による定理の証明
  name: 定理の名前
  n1: 証明に使う１つ目の定理名
  n2: 証明に使う２つ目の定理名
  l: 定理の左辺
  r: 定理の右辺
  crit: critical pair
*)
let proof_using_crit ~name ~n1 ~n2 ~l ~r ~crit ~(constants:My_term.constants option) =
  let constants = begin match constants with
  | None -> My_term.default_constants
  | Some cs -> cs
  end in
  let e = My_term.to_constrexpr_raw (l, r) constants in
  let evars = My_term.variables_except_constants (l, r) constants in
  let e1 = My_term.to_constrexpr_raw (crit, l) constants in
  let e2 = My_term.to_constrexpr_raw (crit, r) constants in
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
  let tactic = tac_prove_by_crit ~evars ~constants ~e1 ~e2 ~r1 ~r2 ~crit ~l ~r in
  let _, progress = Declare.Obls.add_definition ~pm:(Declare.OblState.empty) ~cinfo ~info ~uctx:ustate ~tactic obl_info in
  match progress with
  | Defined _ -> ()
  | _ -> failwith ("Could not prove goal by crit: " ^ (Names.Id.to_string name))

(** 現在のゴールを冗長な規則の書換によって示す。 *)
let tac_prove_by_reduction ~(rewriters : Libnames.qualid list)
                           ~(rewritee : Libnames.qualid)
                           ~(dbg_gl : string) =
  let open Proofview.Notations in
  (*
    項の左右方向に関わらず証明するため、N個の書き換え規則に対して、l2rs として N+1 個のboolの組み合わせを受け取る。
    l2rs[0]  : symmetry. を使用するかどうか
    l2rs[1:] : i個目の cl_rewrite_clause の書き換え方向を -> にするかどうかを l2rs[i] で表す。
    term の形を調べるかtomaの出力を修正すれば事前に書き換え方向は決定できそうだが、実装の簡単のため全ての組み合わせを試す。
   *)
  let tactic_of l2rs =
    Proofview.Goal.enter (fun gl ->
      (* print goal *)
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let concl = Proofview.Goal.concl gl in
      let term = EConstr.to_constr sigma concl in
      print_endline ("@tactic_of: goal: " ^ (Pp.string_of_ppcmds (Printer.pr_constr_env env sigma term)));
    (* 
      print_endline ("@tactic_of: hyps: " ^ (string_of_int (List.length (Proofview.Goal.hyps gl))));
      (* print all hyp names *)
      List.iter (fun hyp_pt -> print_endline (Names.Id.to_string (Context.Named.Declaration.get_id hyp_pt))) (Proofview.Goal.hyps gl); *)
    let use_symmetry = List.hd l2rs in
    let l2rs = List.tl l2rs in
    Tactics.intros <*>
    Tactics.pose_proof (Names.Name (Names.Id.of_string "H")) (EConstr.mkRef (Nametab.global rewritee, EConstr.EInstance.empty)) <*>
    List.fold_left (fun prev cur -> prev <*> cur) Tacticals.tclIDTAC (
      List.map (fun (rewriter, l2r) -> 
        cl_rewrite_clause_innermost rewriter l2r
        ) (List.combine rewriters l2rs)) <*>
    (if use_symmetry then Tactics.symmetry else Tacticals.tclIDTAC) <*>
    Auto.default_auto)
  in
  let rec aux l2rs dbg_cnt =
    Proofview.Goal.enter (fun gl ->
      print_endline ("@tac_prove_by_recuction: hyps: " ^ (string_of_int (List.length (Proofview.Goal.hyps gl))));
      print_endline ("DBG CNT: " ^ (string_of_int dbg_cnt));
      Tacticals.tclIFCATCH
        (try Tacticals.tclPROGRESS (tactic_of l2rs) with Nametab.GlobalizationError qid -> print_endline ("errrr" ^ (Libnames.string_of_qualid qid)); Tacticals.tclFAIL (Pp.str "fl"))
        (fun _ -> Tacticals.tclIDTAC)
        (fun _ ->
          match Devutil.next_binls l2rs with
          | None -> Tacticals.tclFAIL (Pp.str "Could not prove goal by reduction.")
          | Some l2rs -> aux l2rs (dbg_cnt + 1))) in
  aux (List.init (List.length rewriters + 1) (fun _ -> true)) 0

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
  let tactic = tac_prove_by_reduction ~rewriters ~rewritee:applier ~dbg_gl:(Names.Id.to_string name) in
  let _, progress = Declare.Obls.add_definition ~pm:(Declare.OblState.empty) ~cinfo ~info ~uctx:ustate ~tactic obl_info in
  match progress with
  | Defined _ -> ()
  | _ -> failwith ("Could not prove interreduce: " ^ (Names.Id.to_string name))

let assert_crit r1 r2 sp name body axioms constants goal env sigma : unit Proofview.tactic =
  let tac_of at1 at2 =
    Tactics.assert_by (Names.Name.mk_name (Names.Id.of_string name)) body (
      Proofview.Goal.enter (fun gl ->
      let l = fst goal in
      let r = snd goal in
      let n1 = "t" ^ (fst r1) in
      let n2 = "t" ^ (fst r2) in
      let e = My_term.to_constrexpr_raw (l, r) constants in
      let evars = My_term.variables_except_constants (l, r) constants in
      let e1 = My_term.to_constrexpr_raw (sp, l) constants in
      let e2 = My_term.to_constrexpr_raw (sp, r) constants in
      let r1 = Libnames.qualid_of_string n1 in
      let r2 = Libnames.qualid_of_string n2 in
      let env = Global.env () in 
      let sigma = Evd.from_env env in
      let (sigma, body) = Constrintern.interp_constr_evars env sigma e in
      let (sigma, e1) = Constrintern.interp_constr_evars env sigma e1 in
      let (sigma, e2) = Constrintern.interp_constr_evars env sigma e2 in
      tac_single_prove_by_crit ~evars ~constants ~e1 ~e2 ~r1 ~r2 ~crit:sp ~l ~r at1 at2)) in
  let next_pair (x, y) =
    (* fail *) if x = 10 then failwith "assert_crit: fail: Too many pairs."
    else
    if y = 1 then
      (1, x + 1)
    else if x < y then (* 対角線より左側にある点 *)
      (x + 1, y)
    else 
      (x, y - 1) in
  let rec aux (at1, at2) =
  (* let aux (at1, at2) = *)
    (* (tactic_of at1 at2) in *)
    Tacticals.tclIFCATCH
      (try Tacticals.tclPROGRESS (tac_of at1 at2) with exn -> print_endline ("xn: " ^ Printexc.to_string exn); Tacticals.tclFAIL (Pp.str "fl"))
      (fun _ -> Tacticals.tclIDTAC)
      (fun _ -> aux (next_pair (at1, at2))) in
  aux (1, 1)

let tac_of_procedure_for_goal
  (proc : Tomaparser.procedure_for_goal)
  (axioms : Libnames.qualid list)
  (constants : My_term.constants)
  : unit Proofview.tactic =
    let open Tacticals in
    (* example: [add_assert ~name:"H0" ~goal ]*)
    let add_assert ~name ~goal ~strat =
      Proofview.Goal.enter (fun gl -> 
        let env = Proofview.Goal.env gl in
        let sigma = Proofview.Goal.sigma gl in
        print_endline ("gl: " ^ My_term.to_trs (goal));
        (* print length of hyps *)
        let hyps = Proofview.Goal.hyps  gl in
        print_endline ("hyps: " ^ (string_of_int (List.length hyps)));
        let e1 = My_term.to_constrexpr_raw goal constants in
        let _, body = Constrintern.interp_constr_evars env sigma e1 in
        let t = begin match strat with
        | Crit (r1, r2, sp) -> assert_crit r1 r2 sp name body axioms constants goal env sigma
        | _ ->
          Tactics.assert_by (Names.Name.mk_name (Names.Id.of_string name)) body
            (Proofview.Goal.enter (fun gl ->
              let hyps = Proofview.Goal.hyps gl in
              print_endline ("@assert_by hyps: " ^ (string_of_int (List.length hyps)));
              match strat with
              | Axiom ->
                print_endline ("AX: " ^ name);
                tac_prove_by_axiom ~axioms
              | Simp (prev, rewriters) ->
                print_endline ("SIMP: " ^ name);
                tac_prove_by_reduction ~rewriters:(List.map (fun r -> Libnames.qualid_of_string ("H" ^ r)) rewriters)
                                      ~rewritee:(Libnames.qualid_of_string ("H" ^ fst prev)) ~dbg_gl:name
              | Crit (r1, r2, sp) ->
                print_endline ("CRIT: " ^ name);
                try 
                  let e1 = My_term.to_constrexpr_raw (sp, fst goal) constants in
                  let sigma, e1 = Constrintern.interp_constr_evars env sigma e1 in
                  let e2 = My_term.to_constrexpr_raw (sp, fst goal) constants in
                  let sigma, e2 = Constrintern.interp_constr_evars env sigma e2 in
                  let r1 = Libnames.qualid_of_string ("H" ^ fst r1) in
                  let r2 = Libnames.qualid_of_string ("H" ^ fst r2) in
                  tac_prove_by_crit ~l:(fst goal) ~r:(snd goal) ~crit:sp ~constants ~e1 ~e2 ~r1 ~r2 ~evars:(My_term.variables_except_constants goal constants)
              with exn -> print_endline (Printexc.to_string exn); tclFAIL (Pp.str "ECCEE")))
            end in
              (* prove_crit
                ~n1:("H" ^ fst r1)
                ~n2:("H" ^ fst r2)
                ~l:(fst goal)
                ~r:(snd goal)
                ~crit:sp
                ~constants:(Some constants))) in *)
        Proofview.tclIFCATCH t (fun () -> print_endline "<OK>"; tclIDTAC) (fun _ -> tclFAIL (Pp.str "ERR on " ))) in
    let fst3 (f, _, _) = f in
    let tac = tclMAP (fun (rule, strat) ->
      add_assert ~name:("H" ^ fst rule) ~goal:(snd rule) ~strat) (fst3 proc) in
    (* let open Proofview.Notations in *)
    (* print_endline ("GL ID: " ^ (fst (fst (snd proc)))); *)
    tac
    (* <*> (add_assert
        ~name:("H" ^ (fst (fst (snd proc))))
        ~goal:(snd (fst (snd proc)))
        ~strat:(Simp (fst (snd proc), snd (snd proc)))) *)
    (* <*> Tactics.apply (EConstr.mkVar (Names.Id.of_string ("H" ^ (fst (fst (snd proc)))))) *)
      (* いずれかの assert から直ちに示せるので、全て試す。 *)
      (* (let rec aux = function
      | [] -> tclFAIL (Pp.str "Could not prove by any H#.")
      | ((id, _), _) :: tl ->
        let tac = Tactics.apply (EConstr.mkVar (Names.Id.of_string ("H" ^ id))) in
        tclIFCATCH tac
          (fun () -> tclIDTAC)
          (fun _ -> aux tl) in
      aux (fst proc)) *)