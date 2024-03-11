open Plugin.Devutil

let value_exn = function
  | Some v -> v
  | None -> failwith "None"

let expect_none = function
  | Some _ -> failwith "Some"
  | None -> ()

let%expect_test "next_binls: basic" =
  List.iter (fun b -> Printf.printf "%b\n" b) (value_exn (next_binls [true; false; true]));
  [%expect {|
    true
    false
    false
    |}]

let%expect_test "next_binls: corner" =
  List.iter (fun b -> Printf.printf "%b\n" b) (value_exn (next_binls [true; false; false]));
  [%expect {|
    false
    true
    true
    |}]
    
let%expect_test "next_binls: finish" =
  expect_none (next_binls [false; false; false]);
  expect_none (next_binls [false; false]);
  ()