open Plugin.Equation

let%expect_test "Term" =
  Term.to_string (Term.mkApp "f" [Term.mkVar "a"; Term.mkVar "b"])
  |> print_string;
  [%expect {| f (a, b) |}]

let%expect_test "to_string" =
  let v = Term.mkVar and a = Term.mkApp in
  let t =
    create
      ~varnames:["x"]
      ~left:(a "+" [v "a"; v "b"])
      ~right:(v "c")
  in
  print_string (to_string t);
    [%expect {| + (a, b) = c |}];
  print_string (to_string ~arrow:`L2R t);
    [%expect {| + (a, b) -> c |}];
  print_string (to_string ~arrow:`R2L t);
    [%expect {| + (a, b) <- c |}]

let%expect_test "to_string with prods" =
  let v = Term.mkVar and a = Term.mkApp in
  let t =
    create
      ~varnames:["x"; "y"]
      ~left:(a "+" [v "a"; v "b"])
      ~right:(v "c")
  in
  print_string (to_string ~with_prods:true t);
    [%expect {| forall x y, + (a, b) = c |}];
  print_string (to_string ~with_prods:true ~arrow:`L2R t);
    [%expect {| forall x y, + (a, b) -> c |}];
  print_string (to_string ~with_prods:true ~arrow:`R2L t);
    [%expect {| forall x y, + (a, b) <- c |}]
