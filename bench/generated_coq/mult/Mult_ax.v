Parameter G : Set.
Parameter z : G.
Parameter s : G -> G.
Parameter add : G -> G -> G.
Parameter mult : G -> G -> G.

Axiom add_z : forall Y : G, mult z Y = z.
Axiom add_s : forall X Y : G, mult (s X) Y = mult X Y.
Axiom mult_z : forall Y : G, mult z Y = z.
Axiom mult_s : forall X Y : G, mult (s X) Y = mult (add X Y) Y.
