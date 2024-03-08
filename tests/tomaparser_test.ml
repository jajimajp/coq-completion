open Plugin.Tomaparser

let input = "Completed
axioms:
0: +(0(), X0) = X0.
1: +(-(X1), X1) = 0().
2: +(+(X1, X0), X2) = +(X1, +(X0, X2)).
generated rules:
0: +(0(), X0) = X0.
Proof: Axiom.

1: +(-(X1), X1) = 0().
Proof: Axiom.

2: +(+(X1, X0), X2) = +(X1, +(X0, X2)).
Proof: Axiom.

3: +(-(X3), +(X3, X2)) = +(0(), X2).
Proof: A critical pair between equations 2 and 1 with superposition +(+(-(X3), X3), X2).

4: +(-(X3), +(X3, X2)) = X2.
Proof: Rewrite equation 3,
                lhs with equations []
                rhs with equations [0].

5: X4 = +(-(0()), X4).
Proof: A critical pair between equations 4 and 0 with superposition +(-(0()), +(0(), X4)).

6: X4 = +(-(-(X4)), 0()).
Proof: A critical pair between equations 4 and 1 with superposition +(-(-(X4)), +(-(X4), X4)).

7: +(X4, X5) = +(-(-(X4)), X5).
Proof: A critical pair between equations 4 and 4 with superposition +(-(-(X4)), +(-(X4), +(X4, X5))).

8: X6 = +(-(+(X4, X5)), +(X4, +(X5, X6))).
Proof: A critical pair between equations 4 and 2 with superposition +(-(+(X4, X5)), +(+(X4, X5), X6)).

9: X4 = +(X4, 0()).
Proof: Rewrite equation 6,
                lhs with equations []
                rhs with equations [7].

10: -(0()) = 0().
Proof: A critical pair between equations 9 and 5 with superposition +(-(0()), 0()).

11: +(X4, -(X4)) = 0().
Proof: A critical pair between equations 7 and 1 with superposition +(-(-(X4)), -(X4)).

12: +(X4, 0()) = -(-(X4)).
Proof: A critical pair between equations 7 and 9 with superposition +(-(-(X4)), 0()).

13: X4 = +(-(-(X4)), 0()).
Proof: A critical pair between equations 4 and 1 with superposition +(-(-(X4)), +(-(X4), X4)).

14: +(X4, +(-(X4), X7)) = X7.
Proof: A critical pair between equations 7 and 4 with superposition +(-(-(X4)), +(-(X4), X7)).

15: X7 = +(-(+(X4, -(0()))), +(X4, X7)).
Proof: A critical pair between equations 8 and 5 with superposition +(-(+(X4, -(0()))), +(X4, +(-(0()), X7))).

16: X7 = +(-(+(X4, -(X7))), +(X4, 0())).
Proof: A critical pair between equations 8 and 1 with superposition +(-(+(X4, -(X7))), +(X4, +(-(X7), X7))).

17: X6 = +(-(+(-(+(X5, X6)), X5)), 0()).
Proof: A critical pair between equations 8 and 1 with superposition +(-(+(-(+(X5, X6)), X5)), +(-(+(X5, X6)), +(X5, X6))).

18: +(X8, X9) = +(-(+(-(+(X7, X8)), X7)), X9).
Proof: A critical pair between equations 8 and 8 with superposition +(-(+(-(+(X7, X8)), X7)), +(-(+(X7, X8)), +(X7, +(X8, X9)))).

19: +(X7, X8) = +(-(+(X4, -(X7))), +(X4, X8)).
Proof: A critical pair between equations 8 and 4 with superposition +(-(+(X4, -(X7))), +(X4, +(-(X7), +(X7, X8)))).

20: X8 = +(-(+(X4, -(-(X7)))), +(X4, +(X7, X8))).
Proof: A critical pair between equations 8 and 7 with superposition +(-(+(X4, -(-(X7)))), +(X4, +(-(-(X7)), X8))).

21: X9 = +(-(+(X4, +(X7, X8))), +(X4, +(X7, +(X8, X9)))).
Proof: A critical pair between equations 8 and 2 with superposition +(-(+(X4, +(X7, X8))), +(X4, +(+(X7, X8), X9))).

22: X6 = -(+(-(+(X5, X6)), X5)).
Proof: Rewrite equation 17,
                lhs with equations []
                rhs with equations [9].

23: X7 = +(-(+(X4, -(X7))), X4).
Proof: Rewrite equation 16,
                lhs with equations []
                rhs with equations [9].

24: X4 = -(-(X4)).
Proof: Rewrite equation 12,
                lhs with equations [9]
                rhs with equations [].

25: +(X8, -(+(-(X11), X8))) = X11.
Proof: A critical pair between equations 18 and 23 with superposition +(-(+(-(+(-(X11), X8)), -(X11))), -(+(-(X11), X8))).

26: X10 = -(+(X11, -(+(X10, X11)))).
Proof: A critical pair between equations 22 and 18 with superposition -(+(-(+(-(+(X10, X11)), X10)), -(+(X10, X11)))).

27: -(X8) = +(-(+(X4, X8)), X4).
Proof: A critical pair between equations 23 and 24 with superposition +(-(+(X4, -(-(X8)))), X4).

28: +(X8, +(-(+(X7, X8)), X7)) = 0().
Proof: A critical pair between equations 18 and 1 with superposition +(-(+(-(+(X7, X8)), X7)), +(-(+(X7, X8)), X7)).

29: +(-(X8), X9) = -(+(-(X9), X8)).
Proof: A critical pair between equations 22 and 14 with superposition -(+(-(+(X8, +(-(X8), X9))), X8)).

30: +(X7, X8) = -(+(-(X8), -(X7))).
Proof: A critical pair between equations 22 and 4 with superposition -(+(-(+(-(X7), +(X7, X8))), -(X7))).

31: 0() = +(X5, +(X6, -(+(X5, X6)))).
Proof: A critical pair between equations 11 and 2 with superposition +(+(X5, X6), -(+(X5, X6))).

32: X8 = -(+(-(X9), -(+(X8, -(X9))))).
Proof: A critical pair between equations 22 and 23 with superposition -(+(-(+(-(+(X8, -(X9))), X8)), -(+(X8, -(X9))))).

33: X7 = +(-(X9), -(+(-(X7), -(X9)))).
Proof: A critical pair between equations 23 and 23 with superposition +(-(+(-(+(-(X7), -(X9))), -(X7))), -(+(-(X7), -(X9)))).

34: -(X7) = +(-(+(X4, X7)), +(X4, 0())).
Proof: A critical pair between equations 8 and 11 with superposition +(-(+(X4, X7)), +(X4, +(X7, -(X7)))).

35: +(X7, -(X9)) = +(-(+(X9, -(X7))), 0()).
Proof: A critical pair between equations 19 and 11 with superposition +(-(+(X9, -(X7))), +(X9, -(X9))).

36: +(X7, X9) = +(-(+(-(X9), -(X7))), 0()).
Proof: A critical pair between equations 19 and 1 with superposition +(-(+(-(X9), -(X7))), +(-(X9), X9)).

37: +(X7, -(X9)) = -(+(X9, -(X7))).
Proof: Rewrite equation 35,
                lhs with equations []
                rhs with equations [9].

38: +(-(X10), -(X9)) = -(+(X9, X10)).
Proof: A critical pair between equations 37 and 24 with superposition -(+(X9, -(-(X10)))).

39: -(X9) = +(-(-(X10)), -(+(X9, X10))).
Proof: A critical pair between equations 27 and 27 with superposition +(-(+(-(+(X9, X10)), X9)), -(+(X9, X10))).

40: +(X8, -(+(X7, X8))) = +(-(X7), 0()).
Proof: A critical pair between equations 4 and 31 with superposition +(-(X7), +(X7, +(X8, -(+(X7, X8))))).

41: +(X1, +(X0, +(-(+(X1, X0)), X9))) = X9.
Proof: A critical pair between equations 2 and 14 with superposition +(+(X1, X0), +(-(+(X1, X0)), X9)).

42: +(-(+(X10, +(X11, X12))), +(X10, X11)) = -(X12).
Proof: A critical pair between equations 29 and 8 with superposition -(+(-(+(X10, X11)), +(X10, +(X11, X12)))).

43: +(-(X8), X9) = +(-(+(X4, X8)), +(X4, X9)).
Proof: A critical pair between equations 8 and 14 with superposition +(-(+(X4, X8)), +(X4, +(X8, +(-(X8), X9)))).

44: +(X7, -(+(X10, X11))) = -(+(X10, +(X11, -(X7)))).
Proof: A critical pair between equations 37 and 2 with superposition -(+(+(X10, X11), -(X7))).

45: 0() = +(+(X7, X8), +(X9, -(+(X7, +(X8, X9))))).
Proof: A critical pair between equations 31 and 2 with superposition +(+(X7, X8), +(X9, -(+(+(X7, X8), X9)))).

46: 0() = +(X5, +(X7, +(X8, -(+(X5, +(X7, X8)))))).
Proof: A critical pair between equations 31 and 2 with superposition +(X5, +(+(X7, X8), -(+(X5, +(X7, X8))))).

47: 0() = +(X7, +(X8, +(X6, -(+(+(X7, X8), X6))))).
Proof: A critical pair between equations 31 and 2 with superposition +(+(X7, X8), +(X6, -(+(+(X7, X8), X6)))).

48: -(+(X9, +(X10, X11))) = +(-(X11), -(+(X9, X10))).
Proof: A critical pair between equations 27 and 8 with superposition +(-(+(-(+(X9, X10)), +(X9, +(X10, X11)))), -(+(X9, X10))).

49: X6 = +(-(-(X10)), +(-(+(X9, X10)), +(X9, X6))).
Proof: A critical pair between equations 8 and 27 with superposition +(-(+(-(+(X9, X10)), X9)), +(-(+(X9, X10)), +(X9, X6))).

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
38: -(+(X9, X10)) -> +(-(X10), -(X9))" |> String.split_on_char '\n'

let%expect_test "parse" =
  V6.print_procedure (V6.parse input);
  [%expect {|
    Axiom: 0: App{+,[Var{0()};Var{X0}]} = Var{X0}
    Axiom: 1: App{+,[App{-,[Var{X1}]};Var{X1}]} = Var{0()}
    Axiom: 2: App{+,[App{+,[Var{X1};Var{X0}]};Var{X2}]} = App{+,[Var{X1};App{+,[Var{X0};Var{X2}]}]}
    Crit: 3: App{+,[App{-,[Var{X3}]};App{+,[Var{X3};Var{X2}]}]} = App{+,[Var{0()};Var{X2}]} with superposition App{+,[App{+,[App{-,[Var{X3}]};Var{X3}]};Var{X2}]}
    Simp: 4: App{+,[App{-,[Var{X3}]};App{+,[Var{X3};Var{X2}]}]} = Var{X2} by rewriting lhs with , and rhs with 0
    Crit: 5: Var{X4} = App{+,[App{-,[Var{0()}]};Var{X4}]} with superposition App{+,[App{-,[Var{0()}]};App{+,[Var{0()};Var{X4}]}]}
    Crit: 6: Var{X4} = App{+,[App{-,[App{-,[Var{X4}]}]};Var{0()}]} with superposition App{+,[App{-,[App{-,[Var{X4}]}]};App{+,[App{-,[Var{X4}]};Var{X4}]}]}
    Crit: 7: App{+,[Var{X4};Var{X5}]} = App{+,[App{-,[App{-,[Var{X4}]}]};Var{X5}]} with superposition App{+,[App{-,[App{-,[Var{X4}]}]};App{+,[App{-,[Var{X4}]};App{+,[Var{X4};Var{X5}]}]}]}
    Crit: 8: Var{X6} = App{+,[App{-,[App{+,[Var{X4};Var{X5}]}]};App{+,[Var{X4};App{+,[Var{X5};Var{X6}]}]}]} with superposition App{+,[App{-,[App{+,[Var{X4};Var{X5}]}]};App{+,[App{+,[Var{X4};Var{X5}]};Var{X6}]}]}
    Simp: 9: Var{X4} = App{+,[Var{X4};Var{0()}]} by rewriting lhs with , and rhs with 7
    Crit: 10: App{-,[Var{0()}]} = Var{0()} with superposition App{+,[App{-,[Var{0()}]};Var{0()}]}
    Crit: 11: App{+,[Var{X4};App{-,[Var{X4}]}]} = Var{0()} with superposition App{+,[App{-,[App{-,[Var{X4}]}]};App{-,[Var{X4}]}]}
    Crit: 12: App{+,[Var{X4};Var{0()}]} = App{-,[App{-,[Var{X4}]}]} with superposition App{+,[App{-,[App{-,[Var{X4}]}]};Var{0()}]}
    Crit: 13: Var{X4} = App{+,[App{-,[App{-,[Var{X4}]}]};Var{0()}]} with superposition App{+,[App{-,[App{-,[Var{X4}]}]};App{+,[App{-,[Var{X4}]};Var{X4}]}]}
    Crit: 14: App{+,[Var{X4};App{+,[App{-,[Var{X4}]};Var{X7}]}]} = Var{X7} with superposition App{+,[App{-,[App{-,[Var{X4}]}]};App{+,[App{-,[Var{X4}]};Var{X7}]}]}
    Crit: 15: Var{X7} = App{+,[App{-,[App{+,[Var{X4};App{-,[Var{0()}]}]}]};App{+,[Var{X4};Var{X7}]}]} with superposition App{+,[App{-,[App{+,[Var{X4};App{-,[Var{0()}]}]}]};App{+,[Var{X4};App{+,[App{-,[Var{0()}]};Var{X7}]}]}]}
    Crit: 16: Var{X7} = App{+,[App{-,[App{+,[Var{X4};App{-,[Var{X7}]}]}]};App{+,[Var{X4};Var{0()}]}]} with superposition App{+,[App{-,[App{+,[Var{X4};App{-,[Var{X7}]}]}]};App{+,[Var{X4};App{+,[App{-,[Var{X7}]};Var{X7}]}]}]}
    Crit: 17: Var{X6} = App{+,[App{-,[App{+,[App{-,[App{+,[Var{X5};Var{X6}]}]};Var{X5}]}]};Var{0()}]} with superposition App{+,[App{-,[App{+,[App{-,[App{+,[Var{X5};Var{X6}]}]};Var{X5}]}]};App{+,[App{-,[App{+,[Var{X5};Var{X6}]}]};App{+,[Var{X5};Var{X6}]}]}]}
    Crit: 18: App{+,[Var{X8};Var{X9}]} = App{+,[App{-,[App{+,[App{-,[App{+,[Var{X7};Var{X8}]}]};Var{X7}]}]};Var{X9}]} with superposition App{+,[App{-,[App{+,[App{-,[App{+,[Var{X7};Var{X8}]}]};Var{X7}]}]};App{+,[App{-,[App{+,[Var{X7};Var{X8}]}]};App{+,[Var{X7};App{+,[Var{X8};Var{X9}]}]}]}]}
    Crit: 19: App{+,[Var{X7};Var{X8}]} = App{+,[App{-,[App{+,[Var{X4};App{-,[Var{X7}]}]}]};App{+,[Var{X4};Var{X8}]}]} with superposition App{+,[App{-,[App{+,[Var{X4};App{-,[Var{X7}]}]}]};App{+,[Var{X4};App{+,[App{-,[Var{X7}]};App{+,[Var{X7};Var{X8}]}]}]}]}
    Crit: 20: Var{X8} = App{+,[App{-,[App{+,[Var{X4};App{-,[App{-,[Var{X7}]}]}]}]};App{+,[Var{X4};App{+,[Var{X7};Var{X8}]}]}]} with superposition App{+,[App{-,[App{+,[Var{X4};App{-,[App{-,[Var{X7}]}]}]}]};App{+,[Var{X4};App{+,[App{-,[App{-,[Var{X7}]}]};Var{X8}]}]}]}
    Crit: 21: Var{X9} = App{+,[App{-,[App{+,[Var{X4};App{+,[Var{X7};Var{X8}]}]}]};App{+,[Var{X4};App{+,[Var{X7};App{+,[Var{X8};Var{X9}]}]}]}]} with superposition App{+,[App{-,[App{+,[Var{X4};App{+,[Var{X7};Var{X8}]}]}]};App{+,[Var{X4};App{+,[App{+,[Var{X7};Var{X8}]};Var{X9}]}]}]}
    Simp: 22: Var{X6} = App{-,[App{+,[App{-,[App{+,[Var{X5};Var{X6}]}]};Var{X5}]}]} by rewriting lhs with , and rhs with 9
    Simp: 23: Var{X7} = App{+,[App{-,[App{+,[Var{X4};App{-,[Var{X7}]}]}]};Var{X4}]} by rewriting lhs with , and rhs with 9
    Simp: 24: Var{X4} = App{-,[App{-,[Var{X4}]}]} by rewriting lhs with 9, and rhs with
    Crit: 25: App{+,[Var{X8};App{-,[App{+,[App{-,[Var{X11}]};Var{X8}]}]}]} = Var{X11} with superposition App{+,[App{-,[App{+,[App{-,[App{+,[App{-,[Var{X11}]};Var{X8}]}]};App{-,[Var{X11}]}]}]};App{-,[App{+,[App{-,[Var{X11}]};Var{X8}]}]}]}
    Crit: 26: Var{X10} = App{-,[App{+,[Var{X11};App{-,[App{+,[Var{X10};Var{X11}]}]}]}]} with superposition App{-,[App{+,[App{-,[App{+,[App{-,[App{+,[Var{X10};Var{X11}]}]};Var{X10}]}]};App{-,[App{+,[Var{X10};Var{X11}]}]}]}]}
    Crit: 27: App{-,[Var{X8}]} = App{+,[App{-,[App{+,[Var{X4};Var{X8}]}]};Var{X4}]} with superposition App{+,[App{-,[App{+,[Var{X4};App{-,[App{-,[Var{X8}]}]}]}]};Var{X4}]}
    Crit: 28: App{+,[Var{X8};App{+,[App{-,[App{+,[Var{X7};Var{X8}]}]};Var{X7}]}]} = Var{0()} with superposition App{+,[App{-,[App{+,[App{-,[App{+,[Var{X7};Var{X8}]}]};Var{X7}]}]};App{+,[App{-,[App{+,[Var{X7};Var{X8}]}]};Var{X7}]}]}
    Crit: 29: App{+,[App{-,[Var{X8}]};Var{X9}]} = App{-,[App{+,[App{-,[Var{X9}]};Var{X8}]}]} with superposition App{-,[App{+,[App{-,[App{+,[Var{X8};App{+,[App{-,[Var{X8}]};Var{X9}]}]}]};Var{X8}]}]}
    Crit: 30: App{+,[Var{X7};Var{X8}]} = App{-,[App{+,[App{-,[Var{X8}]};App{-,[Var{X7}]}]}]} with superposition App{-,[App{+,[App{-,[App{+,[App{-,[Var{X7}]};App{+,[Var{X7};Var{X8}]}]}]};App{-,[Var{X7}]}]}]}
    Crit: 31: Var{0()} = App{+,[Var{X5};App{+,[Var{X6};App{-,[App{+,[Var{X5};Var{X6}]}]}]}]} with superposition App{+,[App{+,[Var{X5};Var{X6}]};App{-,[App{+,[Var{X5};Var{X6}]}]}]}
    Crit: 32: Var{X8} = App{-,[App{+,[App{-,[Var{X9}]};App{-,[App{+,[Var{X8};App{-,[Var{X9}]}]}]}]}]} with superposition App{-,[App{+,[App{-,[App{+,[App{-,[App{+,[Var{X8};App{-,[Var{X9}]}]}]};Var{X8}]}]};App{-,[App{+,[Var{X8};App{-,[Var{X9}]}]}]}]}]}
    Crit: 33: Var{X7} = App{+,[App{-,[Var{X9}]};App{-,[App{+,[App{-,[Var{X7}]};App{-,[Var{X9}]}]}]}]} with superposition App{+,[App{-,[App{+,[App{-,[App{+,[App{-,[Var{X7}]};App{-,[Var{X9}]}]}]};App{-,[Var{X7}]}]}]};App{-,[App{+,[App{-,[Var{X7}]};App{-,[Var{X9}]}]}]}]}
    Crit: 34: App{-,[Var{X7}]} = App{+,[App{-,[App{+,[Var{X4};Var{X7}]}]};App{+,[Var{X4};Var{0()}]}]} with superposition App{+,[App{-,[App{+,[Var{X4};Var{X7}]}]};App{+,[Var{X4};App{+,[Var{X7};App{-,[Var{X7}]}]}]}]}
    Crit: 35: App{+,[Var{X7};App{-,[Var{X9}]}]} = App{+,[App{-,[App{+,[Var{X9};App{-,[Var{X7}]}]}]};Var{0()}]} with superposition App{+,[App{-,[App{+,[Var{X9};App{-,[Var{X7}]}]}]};App{+,[Var{X9};App{-,[Var{X9}]}]}]}
    Crit: 36: App{+,[Var{X7};Var{X9}]} = App{+,[App{-,[App{+,[App{-,[Var{X9}]};App{-,[Var{X7}]}]}]};Var{0()}]} with superposition App{+,[App{-,[App{+,[App{-,[Var{X9}]};App{-,[Var{X7}]}]}]};App{+,[App{-,[Var{X9}]};Var{X9}]}]}
    Simp: 37: App{+,[Var{X7};App{-,[Var{X9}]}]} = App{-,[App{+,[Var{X9};App{-,[Var{X7}]}]}]} by rewriting lhs with , and rhs with 9
    Crit: 38: App{+,[App{-,[Var{X10}]};App{-,[Var{X9}]}]} = App{-,[App{+,[Var{X9};Var{X10}]}]} with superposition App{-,[App{+,[Var{X9};App{-,[App{-,[Var{X10}]}]}]}]}
    Crit: 39: App{-,[Var{X9}]} = App{+,[App{-,[App{-,[Var{X10}]}]};App{-,[App{+,[Var{X9};Var{X10}]}]}]} with superposition App{+,[App{-,[App{+,[App{-,[App{+,[Var{X9};Var{X10}]}]};Var{X9}]}]};App{-,[App{+,[Var{X9};Var{X10}]}]}]}
    Crit: 40: App{+,[Var{X8};App{-,[App{+,[Var{X7};Var{X8}]}]}]} = App{+,[App{-,[Var{X7}]};Var{0()}]} with superposition App{+,[App{-,[Var{X7}]};App{+,[Var{X7};App{+,[Var{X8};App{-,[App{+,[Var{X7};Var{X8}]}]}]}]}]}
    Crit: 41: App{+,[Var{X1};App{+,[Var{X0};App{+,[App{-,[App{+,[Var{X1};Var{X0}]}]};Var{X9}]}]}]} = Var{X9} with superposition App{+,[App{+,[Var{X1};Var{X0}]};App{+,[App{-,[App{+,[Var{X1};Var{X0}]}]};Var{X9}]}]}
    Crit: 42: App{+,[App{-,[App{+,[Var{X10};App{+,[Var{X11};Var{X12}]}]}]};App{+,[Var{X10};Var{X11}]}]} = App{-,[Var{X12}]} with superposition App{-,[App{+,[App{-,[App{+,[Var{X10};Var{X11}]}]};App{+,[Var{X10};App{+,[Var{X11};Var{X12}]}]}]}]}
    Crit: 43: App{+,[App{-,[Var{X8}]};Var{X9}]} = App{+,[App{-,[App{+,[Var{X4};Var{X8}]}]};App{+,[Var{X4};Var{X9}]}]} with superposition App{+,[App{-,[App{+,[Var{X4};Var{X8}]}]};App{+,[Var{X4};App{+,[Var{X8};App{+,[App{-,[Var{X8}]};Var{X9}]}]}]}]}
    Crit: 44: App{+,[Var{X7};App{-,[App{+,[Var{X10};Var{X11}]}]}]} = App{-,[App{+,[Var{X10};App{+,[Var{X11};App{-,[Var{X7}]}]}]}]} with superposition App{-,[App{+,[App{+,[Var{X10};Var{X11}]};App{-,[Var{X7}]}]}]}
    Crit: 45: Var{0()} = App{+,[App{+,[Var{X7};Var{X8}]};App{+,[Var{X9};App{-,[App{+,[Var{X7};App{+,[Var{X8};Var{X9}]}]}]}]}]} with superposition App{+,[App{+,[Var{X7};Var{X8}]};App{+,[Var{X9};App{-,[App{+,[App{+,[Var{X7};Var{X8}]};Var{X9}]}]}]}]}
    Crit: 46: Var{0()} = App{+,[Var{X5};App{+,[Var{X7};App{+,[Var{X8};App{-,[App{+,[Var{X5};App{+,[Var{X7};Var{X8}]}]}]}]}]}]} with superposition App{+,[Var{X5};App{+,[App{+,[Var{X7};Var{X8}]};App{-,[App{+,[Var{X5};App{+,[Var{X7};Var{X8}]}]}]}]}]}
    Crit: 47: Var{0()} = App{+,[Var{X7};App{+,[Var{X8};App{+,[Var{X6};App{-,[App{+,[App{+,[Var{X7};Var{X8}]};Var{X6}]}]}]}]}]} with superposition App{+,[App{+,[Var{X7};Var{X8}]};App{+,[Var{X6};App{-,[App{+,[App{+,[Var{X7};Var{X8}]};Var{X6}]}]}]}]}
    Crit: 48: App{-,[App{+,[Var{X9};App{+,[Var{X10};Var{X11}]}]}]} = App{+,[App{-,[Var{X11}]};App{-,[App{+,[Var{X9};Var{X10}]}]}]} with superposition App{+,[App{-,[App{+,[App{-,[App{+,[Var{X9};Var{X10}]}]};App{+,[Var{X9};App{+,[Var{X10};Var{X11}]}]}]}]};App{-,[App{+,[Var{X9};Var{X10}]}]}]}
    Crit: 49: Var{X6} = App{+,[App{-,[App{-,[Var{X10}]}]};App{+,[App{-,[App{+,[Var{X9};Var{X10}]}]};App{+,[Var{X9};Var{X6}]}]}]} with superposition App{+,[App{-,[App{+,[App{-,[App{+,[Var{X9};Var{X10}]}]};Var{X9}]}]};App{+,[App{-,[App{+,[Var{X9};Var{X10}]}]};App{+,[Var{X9};Var{X6}]}]}]}
    Completed: 9: App{+,[Var{X4};Var{0()}]} -> Var{X4}
    Completed: 0: App{+,[Var{0()};Var{X0}]} -> Var{X0}
    Completed: 1: App{+,[App{-,[Var{X1}]};Var{X1}]} -> Var{0()}
    Completed: 2: App{+,[App{+,[Var{X1};Var{X0}]};Var{X2}]} -> App{+,[Var{X1};App{+,[Var{X0};Var{X2}]}]}
    Completed: 4: App{+,[App{-,[Var{X3}]};App{+,[Var{X3};Var{X2}]}]} -> Var{X2}
    Completed: 10: App{-,[Var{0()}]} -> Var{0()}
    Completed: 11: App{+,[Var{X4};App{-,[Var{X4}]}]} -> Var{0()}
    Completed: 24: App{-,[App{-,[Var{X4}]}]} -> Var{X4}
    Completed: 14: App{+,[Var{X4};App{+,[App{-,[Var{X4}]};Var{X7}]}]} -> Var{X7}
    Completed: 38: App{-,[App{+,[Var{X9};Var{X10}]}]} -> App{+,[App{-,[Var{X10}]};App{-,[Var{X9}]}]}|}]