 Load "DS_Axioms".

Section dh_auth.

(*************DH-Authentication ********************)

(******* oracle reveals false always*********************)

Definition phi10 := [msg (G 0); msg (g 0); msg (pk (N 3)); msg (pk (N 4))].

Definition mphi10 := (conv_mylist_listm phi10).
Definition grn (n:nat) := (exp (G 0) (g 0) (r n)).
Definition x1 := (f mphi10).

(******start state*************)

Definition qa00 :=   (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) (grn 1) (if_then_else_M (EQ_M (to x1) (i 2)) (pair (grn 2) (sign (sk (N 4))  (pair (grn 2) x1))) O)).
(********phi1****)

Definition phi11 := phi10 ++ [msg qa00].

Definition mphi11 := (conv_mylist_listm phi11).
Definition x2 := (f mphi11). 

Definition qa10 :=  (if_then_else_M ((EQ_M (to x2) (i 1))& (ver (pk (N 4)) (pair (pi1 (x2))  (grn 1))   (pi2 (x2)))) (sign (sk (N 3)) (pair  (grn 1) (pi1 (x2))))  O ).

Definition qa01:=  (if_then_else_M (EQ_M (to x2) (i 2))& (ver (pk (N 3)) (pair (grn 1) (pi1 x2)) x2) acc O) .


Definition qa00_s :=  (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qa10 (if_then_else_M (EQ_M (to x1) (i 2)) qa01 O)).
(*********phi2*******)

Definition phi12:= phi11 ++ [msg qa00_s].


Definition mphi12 := (conv_mylist_listm phi12).
Definition x3 := (f mphi12).


Definition qa20 :=  (if_then_else_M (EQ_M (reveal x3) (i 2))& (notb (EQ_M (pi1(x2)) (grn 1)) & (EQ_M x1 (grn 1)))  O O ).

Definition qa02 := (if_then_else_M (EQ_M (reveal x3) (i 2))& (notb ((EQ_M (pi1(x2)) (grn 1))) &  (EQ_M x1 (grn 1)))  O O ).





Definition qa10_s :=    (if_then_else_M ((EQ_M (to x2) (i 1))& (ver (pk (N 4)) (pair (pi1 (x2))  (grn 1)) (pi2 x2)))  qa20 O ).

Definition qa01_s := (if_then_else_M (EQ_M (to x2) (i 2))& (ver (pk (N 3)) (pair x1 (grn 1)) x2)& (EQ_M (pi1(x2)) (grn 1)) & (EQ_M x1 (grn 1)) qa02 O).

Definition qa00_ss :=  (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qa10_s (if_then_else_M (EQ_M (to x1) (i 2)) qa01_s O)).

(**************phi3***********)

Definition phi13 := phi12 ++ [msg qa00_ss].



(***********protocol 2: reveals TRUE if there is an attack***************)
(*************************************************************************)


Definition qb20 :=  (if_then_else_M (EQ_M (reveal x3) (i 2))& (notb (EQ_M (pi1(x2)) (grn 1)) & (EQ_M x1 (grn 1)))  O O ).

Definition qb02 := (if_then_else_M (EQ_M (reveal x3) (i 2))& (notb (EQ_M (pi1(x2)) (grn 1)) & (EQ_M x1 (grn 1))) new O ).

Definition qb10_s :=    (if_then_else_M ((EQ_M (to x2) (i 1))& (ver (pk (N 4)) (pair (pi1 (x2))  (grn 1)) (pi2 x2)))  qb20 O ).

Definition qb01_s := (if_then_else_M (EQ_M (to x2) (i 2))& (ver (pk (N 3)) (pair x1 (grn 1)) x2)& (EQ_M (pi1(x2)) (grn 1)) & (EQ_M x1 (grn 1)) qb02 O).

Definition qb00_ss :=  (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qb10_s (if_then_else_M (EQ_M (to x1) (i 2)) qb01_s O)).

(**************phi3***********)

Definition phi23 := phi12 ++ [msg qb00_ss].


(******************** Two protocols: authentication successful and the case in which authentication fails are indistinguishable******************)

Theorem IND_DH_AUTH:   phi13 #### phi23.
Proof. unfold phi13, phi23, phi12, phi11, phi10. repeat unfold qa00, qa10 , qa01, qa20, qa02, qa10_s, qa01_s, qa00_s, qa00_ss.
simpl.
repeat unfold qb20, qb02, qb10_s, qb01_s, qb00_ss.

assert(trm3: (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M
            (EQ_M (to x2) (i 1)) & (ver (pk (N 4)) (pair (pi1 x2) (grn 1)) (pi2 x2))
            (if_then_else_M
               (EQ_M (reveal x3) (i 2)) &
               (notb (EQ_M (pi1 x2) (grn 1)) & (EQ_M x1 (grn 1))) O O) O)
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M
               (((EQ_M (to x2) (i 2)) & (ver (pk (N 3)) (pair x1 (grn 1)) x2)) &
                (EQ_M (pi1 x2) (grn 1))) & (EQ_M x1 (grn 1))
               (if_then_else_M
                  (EQ_M (reveal x3) (i 2)) &
                  (notb (EQ_M (pi1 x2) (grn 1)) & (EQ_M x1 (grn 1))) O O) O) O)) # (if_then_else_M (EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)
         (if_then_else_M
            (EQ_M (to x2) (i 1)) & (ver (pk (N 4)) (pair (pi1 x2) (grn 1)) (pi2 x2))
            (if_then_else_M
               (EQ_M (reveal x3) (i 2)) &
               (notb (EQ_M (pi1 x2) (grn 1)) & (EQ_M x1 (grn 1))) O O) O)
         (if_then_else_M (EQ_M (to x1) (i 2))
            (if_then_else_M
               (((EQ_M (to x2) (i 2)) & (ver (pk (N 3)) (pair x1 (grn 1)) x2)) &
                (EQ_M (pi1 x2) (grn 1))) & (EQ_M x1 (grn 1))
               (if_then_else_M
                  (EQ_M (reveal x3) (i 2)) &
                  (notb (EQ_M (pi1 x2) (grn 1)) & (EQ_M x1 (grn 1))) new O) O) O))).



assert(vef: (ver (pk (N 3)) (pair x1 (grn 1)) x2) ## FAlse).


pose proof(UFCMA 3 0 []  (pair x1 (grn 1)) x2).

simpl in H.


assert(H1: true = true /\ true = true  /\ true = true /\ 0 = 0).
repeat split. apply H in H1.
apply H1.
rewrite vef.

assert(pf:  (((EQ_M (to x2) (i 2)) & (FAlse)) & (EQ_M (pi1 x2) (grn 1))) &
            (EQ_M x1 (grn 1)) ## FAlse).
rewrite andB_FAlse_r with (b:= (EQ_M (to x2) (i 2))).
rewrite andB_FAlse_l with (b:= (EQ_M (pi1 x2) (grn 1))).
rewrite andB_FAlse_l with (b:= (EQ_M x1 (grn 1))). reflexivity.
rewrite pf.
repeat rewrite IFFALSE_M. reflexivity.  rewrite trm3. reflexivity. Qed.

End dh_auth.
Eval compute in x1.