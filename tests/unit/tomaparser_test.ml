open Plugin.Tomaparser

let%expect_test "parse_rewstep" =
  let pr rs = match rs with
    | None -> print_endline "None"
    | Some ({ rule; pos; _ }) -> Printf.printf "%s %s\n" rule (String.concat ";" (List.map string_of_int pos))
  in
  let input = "- lhs by equation 0 L->R at [1]" in
  pr (parse_rewstep input);
  [%expect {| 0 1 |}];
  let input = "- rhs by equation 0 R->L at [0,1]" in
  pr (parse_rewstep input);
  [%expect {| 0 0;1 |}];
  let input = "- rhs by equation 0 L->R at []" in
  pr (parse_rewstep input);
  [%expect {| 0 |}]


let input =
  {|Completed
order:
LPO with precedence: ___false > ___true > - > + > 0
axioms:
0: +(0(), X0) = X0.
1: +(-(X1), X1) = 0().
2: +(+(X1, X0), X2) = +(X1, +(X0, X2)).
generated rules:
0: +(0(), X0) -> X0.
Proof: Axiom.

1: +(-(X1), X1) -> 0().
Proof: Axiom.

2: +(+(X1, X0), X2) -> +(X1, +(X0, X2)).
Proof: Axiom.

3: +(-(X3), +(X3, X2)) -> +(0(), X2).
Proof: A critical pair between equations 2 and 1 with superposition +(+(-(X3), X3), X2).

4: +(-(X3), +(X3, X2)) -> X2.
Proof: Rewrite equation 3,
- rhs by equation 0 L->R at []

5: X4 <- +(-(0()), X4).
Proof: A critical pair between equations 4 and 0 with superposition +(-(0()), +(0(), X4)).

6: X4 <- +(-(-(X4)), 0()).
Proof: A critical pair between equations 4 and 1 with superposition +(-(-(X4)), +(-(X4), X4)).

7: +(X4, X5) <- +(-(-(X4)), X5).
Proof: A critical pair between equations 4 and 4 with superposition +(-(-(X4)), +(-(X4), +(X4, X5))).

8: X6 <- +(-(+(X4, X5)), +(X4, +(X5, X6))).
Proof: A critical pair between equations 4 and 2 with superposition +(-(+(X4, X5)), +(+(X4, X5), X6)).

9: X4 <- +(X4, 0()).
Proof: Rewrite equation 6,
- rhs by equation 7 L->R at []

10: -(0()) -> 0().
Proof: A critical pair between equations 9 and 5 with superposition +(-(0()), 0()).

11: +(X4, -(X4)) -> 0().
Proof: A critical pair between equations 7 and 1 with superposition +(-(-(X4)), -(X4)).

12: +(X4, 0()) <- -(-(X4)).
Proof: A critical pair between equations 7 and 9 with superposition +(-(-(X4)), 0()).

14: +(X4, +(-(X4), X7)) -> X7.
Proof: A critical pair between equations 7 and 4 with superposition +(-(-(X4)), +(-(X4), X7)).

19: +(X7, X8) <- +(-(+(X4, -(X7))), +(X4, X8)).
Proof: A critical pair between equations 8 and 4 with superposition +(-(+(X4, -(X7))), +(X4, +(-(X7), +(X7, X8)))).

24: X4 <- -(-(X4)).
Proof: Rewrite equation 12,
- lhs by equation 9 L->R at []

35: +(X7, -(X9)) <- +(-(+(X9, -(X7))), 0()).
Proof: A critical pair between equations 19 and 11 with superposition +(-(+(X9, -(X7))), +(X9, -(X9))).

37: +(X7, -(X9)) <- -(+(X9, -(X7))).
Proof: Rewrite equation 35,
- rhs by equation 9 L->R at []

38: +(-(X10), -(X9)) <- -(+(X9, X10)).
Proof: A critical pair between equations 37 and 24 with superposition -(+(X9, -(-(X10)))).

ES:
9: +(X4, 0()) -> X4
0: +(0(), X0) -> X0
1: +(-(X1), X1) -> 0()
2: +(+(X1, X0), X2) -> +(X1, +(X0, X2))
4: +(-(X3), +(X3, X2)) -> X2
10: -(0()) -> 0()
11: +(X4, -(X4)) -> 0()
24: -(-(X4)) -> X4
14: +(X4, +(-(X4), X7)) -> X7
38: -(+(X9, X10)) -> +(-(X10), -(X9))
|}
  |> String.split_on_char '\n'

let%expect_test "parse" =
  print_procedure (parse input);
  [%expect
    {|
   order: ___false > ___true > - > + > 0
   Axiom: 0: +(0,X0) -> X0
   Axiom: 1: +(-(X1),X1) -> 0
   Axiom: 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2))
   Crit: 3: +(-(X3),+(X3,X2)) -> +(0,X2) with 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2)) and 1: +(-(X1),X1) -> 0 with superposition +(+(-(X3),X3),X2)
   Simp: 4: +(-(X3),+(X3,X2)) -> X2 with 0
   Crit: 5: +(-(0),X4) -> X4 with 0: +(0,X0) -> X0 and 4: +(-(X3),+(X3,X2)) -> X2 with superposition +(-(0),+(0,X4))
   Crit: 6: +(-(-(X4)),0) -> X4 with 1: +(-(X1),X1) -> 0 and 4: +(-(X3),+(X3,X2)) -> X2 with superposition +(-(-(X4)),+(-(X4),X4))
   Crit: 7: +(-(-(X4)),X5) -> +(X4,X5) with 4: +(-(X3),+(X3,X2)) -> X2 and 4: +(-(X3),+(X3,X2)) -> X2 with superposition +(-(-(X4)),+(-(X4),+(X4,X5)))
   Crit: 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2)) and 4: +(-(X3),+(X3,X2)) -> X2 with superposition +(-(+(X4,X5)),+(+(X4,X5),X6))
   Simp: 9: +(X4,0) -> X4 with 7
   Crit: 10: -(0) -> 0 with 9: +(X4,0) -> X4 and 5: +(-(0),X4) -> X4 with superposition +(-(0),0)
   Crit: 11: +(X4,-(X4)) -> 0 with 7: +(-(-(X4)),X5) -> +(X4,X5) and 1: +(-(X1),X1) -> 0 with superposition +(-(-(X4)),-(X4))
   Crit: 12: -(-(X4)) -> +(X4,0) with 9: +(X4,0) -> X4 and 7: +(-(-(X4)),X5) -> +(X4,X5) with superposition +(-(-(X4)),0)
   Crit: 14: +(X4,+(-(X4),X7)) -> X7 with 7: +(-(-(X4)),X5) -> +(X4,X5) and 4: +(-(X3),+(X3,X2)) -> X2 with superposition +(-(-(X4)),+(-(X4),X7))
   Crit: 19: +(-(+(X4,-(X7))),+(X4,X8)) -> +(X7,X8) with 4: +(-(X3),+(X3,X2)) -> X2 and 8: +(-(+(X4,X5)),+(X4,+(X5,X6))) -> X6 with superposition +(-(+(X4,-(X7))),+(X4,+(-(X7),+(X7,X8))))
   Simp: 24: -(-(X4)) -> X4 with 9
   Crit: 35: +(-(+(X9,-(X7))),0) -> +(X7,-(X9)) with 11: +(X4,-(X4)) -> 0 and 19: +(-(+(X4,-(X7))),+(X4,X8)) -> +(X7,X8) with superposition +(-(+(X9,-(X7))),+(X9,-(X9)))
   Simp: 37: -(+(X9,-(X7))) -> +(X7,-(X9)) with 9
   Crit: 38: -(+(X9,X10)) -> +(-(X10),-(X9)) with 24: -(-(X4)) -> X4 and 37: -(+(X9,-(X7))) -> +(X7,-(X9)) with superposition -(+(X9,-(-(X10))))
   Completed: 9: +(X4,0) -> X4
   Completed: 0: +(0,X0) -> X0
   Completed: 1: +(-(X1),X1) -> 0
   Completed: 2: +(+(X1,X0),X2) -> +(X1,+(X0,X2))
   Completed: 4: +(-(X3),+(X3,X2)) -> X2
   Completed: 10: -(0) -> 0
   Completed: 11: +(X4,-(X4)) -> 0
   Completed: 24: -(-(X4)) -> X4
   Completed: 14: +(X4,+(-(X4),X7)) -> X7
   Completed: 38: -(+(X9,X10)) -> +(-(X10),-(X9))
    |}]

let input2 =
  {|
Success
order:
LPO with precedence: c1 > + > - > 0
axioms:
0: +(0(), X0) = X0.
1: +(-(X1), X1) = 0().
2: +(+(X1, X0), X2) = +(X1, +(X0, X2)).
generated rules:
1: +(-(X1), X1) -> 0().
Proof: Axiom.

3: +(-(c1()), c1()) = 0().
Proof: Rewrite lhs with equations [1]
               rhs with equations [].
|}
  |> String.split_on_char '\n'

let%expect_test "parse with goal" =
  let prs, _, _ = parse_for_goal input2 in
  print_proofs prs;
  [%expect {|
    Axiom: 1: +(-(X1),X1) -> 0|}]
