Load "AUX_AXIOMS".

(***********Equational theory for DDH**************************************)
(**************************************************************************)

Axiom proj1: forall (m1 m2 :message),  ((pi1 (pair m1 m2))  # m1).
Axiom proj2: forall (m1 m2 : message), ( (pi2 (pair m1 m2)) # m2) .
Axiom commexp: forall (x y g G: message), ( (exp G (exp G g x) y) # (exp G (exp G g y) x)).
