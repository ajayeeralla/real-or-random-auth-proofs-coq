Load "IFIDEMP".


(*****************IFMORPH************************************************************************************)
(*******f ( ...., if b then x else y,...........) = if b then f(......,x,.........) else f (.....,y,.....)****)
(****** f(u, if b then x else y, z) = if b then f(u, x, z) else f(u,y,z)**************************************)

(*Theorem IFMORPH_M:  forall (m n n1 :nat) (ml1 : mylist  m)(x y:message) (ml2 : mylist n) (f: mylist (m + (1+n)) ->message), 
                ( f (ml1 ++[msg (if_then_elsem_ (Bvar n)  x y)] ++ ml2) ) # (if_then_elsem_ (Bvar n) (f(ml1 ++[msg x]++ml2)) (f(ml1 ++[msg y]++ml2))).
Proof.
intros.
rewrite <- IFSAME_M with (b:= (Bvar n)) (x:= f (ml1 ++[msg (if_then_elsem_ (Bvar n)  x y)] ++ ml2 )).
simpl.
rewrite IFEVAL_M.
rewrite subinlist with (n:= n)(b:= TRue)(f:=f) (ml := (ml1 ++ (msg (if_then_elsem_ (Bvar n) x y) :: ml2))).
rewrite subconct.
simpl. 
rewrite subinmsg.
simpl.
rewrite <- beq_nat_refl.
pose proof(IFEVAL_M).

(***setoid_replace  (if_then_elsem_ TRue ((n := TRue)(x)) ((n := TRue)(y))) with ((n := TRue)(x)) using relation EQm. 
setoid_replace (if_then_elsem_ TRue ((n := TRue)(x)) ((n := TRue)(y))) with ((n := TRue)(x)) using relation EQm.**)
(*rewrite IFTRUE_M *)
rewrite subinlist with (n:= n)(b:= FAlse)(f:=f) (ml := (ml1 ++ (msg (if_then_elsem_ (Bvar n) x y) :: ml2))).
rewrite subconct.
simpl.
rewrite subinmsg. simpl.
rewrite <- beq_nat_refl.
(*rewrite IFFALSE_M.*)
rewrite IFEVAL_M with (t1:= (f (ml1 ++ msg x :: ml2)))(t2 := (f (ml1 ++ msg y :: ml2))).
rewrite subinlist with (n:= n)(b:= TRue)(f:=f) (ml := (ml1 ++ (msg  x ) :: ml2)).
rewrite subconct.
simpl.
rewrite subinmsg.
rewrite subinlist with (n:= n)(b:= FAlse)(f:=f) (ml := (ml1 ++ (msg  y ) :: ml2)).
rewrite subconct.
simpl.
rewrite subinmsg.
pose proof(IFTRUE_M ((n := TRue)(x)) ((n := TRue)(y))).
assert(H1 : (msg (if_then_elsem_ TRue ((n := TRue)(x)) ((n := TRue)(y)))) ### (msg ((n := TRue)(x)))).
rewrite H0. reflexivity.
rewrite H1.
assert( H2 : (msg (if_then_elsem_ FAlse ((n := FAlse)(x)) ((n := FAlse)(y)))) ### (msg ((n := FAlse)(y)))).
rewrite IFFALSE_M.
reflexivity.
rewrite H2. reflexivity.
Qed.



Theorem IFMORPH_B:  forall (m n n1 :nat) (ml1 : mylist  m)(b1 b2: Bool) (ml2 : mylist n) (f: mylist (m + (1+n)) ->Bool), 
             ( f (ml1 ++[bol (if_then_elseb_ (Bvar n)  b1 b2)] ++ ml2) ) ## (if_then_elseb_ (Bvar n) (f(ml1 ++[bol  b1]++ml2)) (f(ml1 ++[bol b2]++ml2))).

Proof. 
intros.
rewrite <- IFSAME_B with (b:= (Bvar n)) (b1:= f (ml1 ++[bol (if_then_elseb_ (Bvar n)  b1 b2)] ++ ml2 )).
simpl.
rewrite IFEVAL_B.
rewrite subinlist1 with (n:= n)(b:= TRue)(f:=f) (ml := (ml1 ++ (bol (if_then_elseb_ (Bvar n) b1 b2) :: ml2))).
rewrite subconct.
simpl. simpl.
 simpl.
rewrite subinbol.
simpl.
rewrite <- beq_nat_refl.
rewrite subinlist1 with (n:= n)(b:= FAlse)(f:=f) (ml := (ml1 ++ (bol (if_then_elseb_ (Bvar n) b1 b2) :: ml2))).
rewrite subconct.
simpl.
rewrite subinbol. simpl.
rewrite <- beq_nat_refl.
rewrite IFEVAL_B with (b1:= (f (ml1 ++ bol b1 :: ml2)))(b2 := (f (ml1 ++ bol b2 :: ml2))).
rewrite subinlist1 with (n:= n)(b:= TRue)(f:=f) (ml := (ml1 ++ (bol b1 ) :: ml2)).
rewrite subconct.
simpl.
rewrite subinbol.
rewrite subinlist1 with (n:= n)(b:= FAlse)(f:=f) (ml := (ml1 ++ (bol  b2) :: ml2)).
rewrite subconct.
simpl.
rewrite subinbol.
pose proof(IFTRUE_B ([n := TRue](b1)) ([n := TRue](b2))).
assert(H1 : (bol (if_then_elseb_ TRue ([n := TRue](b1)) ([n := TRue](b2)))) ### (bol ([n := TRue](b1)))).
rewrite H. reflexivity.
rewrite H1.
assert( H2 : (bol (if_then_elseb_ FAlse ([n := FAlse](b1)) ([n := FAlse](b2)))) ### (bol ([n := FAlse](b2)))).
pose proof(IFFALSE_B ([n := FAlse](b1)) ([n := FAlse](b2))).
rewrite H0.
reflexivity.
rewrite H2. reflexivity.
Qed.
*)


Theorem IFMORPH_M1: forall ( x y z : message) (n1 n2:nat),
(if_then_else_M (Bvar n2)(if_then_else_M (Bvar n1)  x y) z) # (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2)  x  z) (if_then_else_M  (Bvar n2) y z) ).
Proof.
intros.
rewrite <- IFSAME_M with (b:= (Bvar n1)) (x:= (if_then_else_M (Bvar n2) (if_then_else_M (Bvar n1) x y) z)).
rewrite IFEVAL_M.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
rewrite IFEVAL_M with (t1:= (if_then_else_M (Bvar n2) x z))(t2:= (if_then_else_M (Bvar n2) y z)).
simpl.
reflexivity.
Qed.

Theorem IFMORPH_B1: forall ( b b1 b2 : Bool) (n1 n2:nat) ,
 (if_then_else_B (Bvar n2)(if_then_else_B (Bvar n1)  b b1) b2)  ## (if_then_else_B (Bvar n1) (if_then_else_B (Bvar n2)  b  b2) (if_then_else_B  (Bvar n2) b1 b2) ).
Proof.
intros.
rewrite <- IFSAME_B with (b:= (Bvar n1)) (b1:= (if_then_else_B (Bvar n2) (if_then_else_B (Bvar n1) b b1) b2)).
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with (n:=n1)(b1:= (if_then_else_B (Bvar n2) b b2))(b2:= (if_then_else_B (Bvar n2) b1 b2)).
simpl.
reflexivity.
Qed.
(************f(if b then x else y, z , z1) = if b then f(x,z,z1) else f(x,y,z1)****************)

Theorem IFMORPH_B2: forall (n:nat)(b1 b2 b3 b4 : Bool) , 
(if_then_else_B (if_then_else_B (Bvar n) b1 b2 ) b3 b4)  ##  (if_then_else_B (Bvar n) (if_then_else_B  b1  b3 b4 ) (if_then_else_B  b2 b3 b4) ).
Proof.
intros.
pose proof (IFSAME_B).
rewrite <- IFSAME_B with (b:= (Bvar n)) (b1:=(if_then_else_B (if_then_else_B (Bvar n) b1 b2 ) b3 b4)).
pose proof(IFEVAL_B).
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with (b1 := (if_then_else_B b1 b3 b4))(b2:= (if_then_else_B b2 b3 b4)).
simpl.
reflexivity.
Qed.

Theorem IFMORPH_M2: forall (n:nat)(b1 b2 :Bool)(y z : message), 
 (if_then_else_M (if_then_else_B (Bvar n) b1 b2 ) y z)  #(if_then_else_M (Bvar n) (if_then_else_M  b1  y z ) (if_then_else_M  b2 y z) ).
Proof.
intros.
rewrite <- IFSAME_M with (b:=(Bvar n))(x:= if_then_else_M (if_then_else_B (Bvar n) b1 b2) y z).
rewrite IFEVAL_M.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_M with (t1:=  (if_then_else_M b1 y z))(t2:= (if_then_else_M b2 y z)).
simpl.
reflexivity.
Qed.

(***************f(if b then x else y, z)= if b then f(x,z) else f(y,z)**************************************)

Theorem IFMORPH_B3: forall  (n n1 n2 n3 :nat), ( EQ_B (if_then_else_B (Bvar n) (Bvar n1) (Bvar n2)) (Bvar n3)) ##  (if_then_else_B (Bvar n) (EQ_B (Bvar n1) (Bvar n3) ) (EQ_B (Bvar n2) (Bvar n3))).
Proof.
intros.
rewrite <- IFSAME_B with (b:=(Bvar n))( b1:= EQ_B (if_then_else_B (Bvar n) (Bvar n1) (Bvar n2)) (Bvar n3)).
rewrite IFEVAL_B.
simpl. rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with (b1:= (EQ_B (Bvar n1) (Bvar n3)))(b2:= (EQ_B (Bvar n2) (Bvar n3))).
simpl.
reflexivity.
Qed.


Theorem IFMORPH_M3: forall  (n n1 n2 n3 :nat), ( EQ_M (if_then_else_M (Bvar n) (Mvar n1) (Mvar n3))  (if_then_else_M (Bvar n) (Mvar n2) (Mvar n3))) ## ( if_then_else_B (Bvar n) (EQ_M (Mvar n1)  (if_then_else_M (Bvar n) (Mvar n2) (Mvar n3) )) (EQ_M (Mvar n3)  (if_then_else_M (Bvar n) (Mvar n2) (Mvar n3)))). 
Proof.
intros.
rewrite <- IFSAME_B with (b:=(Bvar n))( b1:= EQ_M (if_then_else_M (Bvar n) (Mvar n1) (Mvar n3))  (if_then_else_M (Bvar n) (Mvar n2) (Mvar n3))).
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M .
rewrite IFTRUE_M.
rewrite IFFALSE_M.
rewrite IFEVAL_B with (b1:= (EQ_M (Mvar n1) (if_then_else_M (Bvar n) (Mvar n2) (Mvar n3))))(b2:= (EQ_M (Mvar n3) (if_then_else_M (Bvar n) (Mvar n2) (Mvar n3)))).
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
reflexivity.
Qed.



Theorem IFMORPH_M5 : forall (n1 n2 n3 :nat) (m1 m2 m3 m4: message),  (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2) m1 m2 ) (if_then_else_M (Bvar n3) m3 m4)) # (if_then_else_M (Bvar n2) (if_then_else_M (Bvar n1) m1 (if_then_else_M (Bvar n3) m3 m4)) (if_then_else_M (Bvar n1) m2 (if_then_else_M (Bvar n3) m3 m4))).

Proof. intros. 
pose proof(IFSAME_M (Bvar n2) (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2) m1 m2 ) (if_then_else_M (Bvar n3) m3 m4))).
rewrite IFEVAL_M with (n:= n2) (t1:= (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2) m1 m2 ) (if_then_else_M (Bvar n3) m3 m4))) (t2 := (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2) m1 m2 ) (if_then_else_M (Bvar n3) m3 m4))) in H.
simpl in H.
repeat rewrite <- beq_nat_refl in H.
rewrite <-H. 

rewrite IFEVAL_M with (n:= n2) (t1:= (if_then_else_M (Bvar n1) m1 (if_then_else_M (Bvar n3) m3 m4))) (t2 := (if_then_else_M (Bvar n1) m2 (if_then_else_M (Bvar n3) m3 m4))).
simpl. rewrite  IFTRUE_M, IFFALSE_M.
reflexivity. Qed.


Theorem IFMORPH_M6 : forall(n1 n2 :nat) (m1 m2 m3:message), (if_then_else_M (Bvar n1) m1 (if_then_else_M (Bvar n2) m2 m3)) # (if_then_else_M (Bvar n2) (if_then_else_M (Bvar n1) m1 m2) (if_then_else_M (Bvar n1)  m1 m3)).

Proof. intros.  pose proof(IFSAME_M (Bvar n2)  (if_then_else_M (Bvar n1) m1 (if_then_else_M (Bvar n2) m2 m3))).
rewrite IFEVAL_M in H.

simpl in H. repeat rewrite <- beq_nat_refl in H.
rewrite  IFTRUE_M, IFFALSE_M in H.
rewrite <-H. clear H.
rewrite IFEVAL_M with (t1:= (if_then_else_M (Bvar n1) m1 m2)).
simpl. reflexivity. Qed.





Axiom IFMORPH_B4: forall  (n1:nat) (b1 b2 b3:Bool), (if_then_else_B (Bvar n1) b1 (if_then_else_B (Bvar (n1+1)) b2 b3))  ## (if_then_else_B (Bvar (n1+1)) (if_then_else_B (Bvar n1) b1 b2) (if_then_else_B (Bvar n1) b1 b3)) .




