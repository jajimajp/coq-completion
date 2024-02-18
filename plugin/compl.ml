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

let complete ~axioms ~hint_db_name ~ops =
  let axioms = List.map constr_of_qualid axioms in
  (* path を付加する (例: "e" => "AutoEqProver.Test.e") *)
  let ops = List.map (fun op ->
    op |> Nametab.global |> Names.GlobRef.print |> Pp.string_of_ppcmds) ops in
  Toma.toma axioms ops