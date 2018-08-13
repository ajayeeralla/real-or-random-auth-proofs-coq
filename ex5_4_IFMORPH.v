(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                   University of Missouri-Columbia.                   *)
(*                                                                      *)
(*                                                                      *)
(*                                                                      *)
(************************************************************************)


Load "ex5_4_IFIDEMP".

(** This library defines several theorems of [IFMORPH] and the proofs. Notice that we use [#] (resp. [##]) for [message] (resp. [Bool]) in lieu of [=].
 
[(if b then (if b' then x else y) else z) = (if b' then (if b then x else z) else (if b then y else z))]. *)
 
Theorem IFMORPH_M1: forall ( x y z : message) (n1 n2:nat),
(ifm (Bvar n2)(ifm (Bvar n1)  x y) z) # (ifm (Bvar n1) (ifm (Bvar n2)  x  z) (ifm  (Bvar n2) y z) ).
Proof.
intros.
rewrite <- IFSAME_M with (b:= (Bvar n1)) (x:= (ifm (Bvar n2) (ifm (Bvar n1) x y) z)).
rewrite IFEVAL_M.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
rewrite IFEVAL_M with (t1:= (ifm (Bvar n2) x z))(t2:= (ifm (Bvar n2) y z)).
simpl.
reflexivity.
Qed.

Theorem IFMORPH_B1: forall ( b b1 b2 : Bool) (n1 n2:nat) ,
 (ifb (Bvar n2)(ifb (Bvar n1)  b b1) b2)  ## (ifb (Bvar n1) (ifb (Bvar n2)  b  b2) (ifb  (Bvar n2) b1 b2) ).
Proof.
intros.
rewrite <- IFSAME_B with (b:= (Bvar n1)) (b1:= (ifb (Bvar n2) (ifb (Bvar n1) b b1) b2)).
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with (n:=n1)(b1:= (ifb (Bvar n2) b b2))(b2:= (ifb (Bvar n2) b1 b2)).
simpl.
reflexivity.
Qed.
(**For a function [f:Bool -> Bool-> Bool], we have [f(if b then x else y, z , z1) = if b then f(x,z,z1) else f(x,y,z1)] *)

Theorem IFMORPH_B2: forall (n:nat)(b1 b2 b3 b4 : Bool) , 
(ifb (ifb (Bvar n) b1 b2 ) b3 b4)  ##  (ifb (Bvar n) (ifb  b1  b3 b4 ) (ifb  b2 b3 b4) ).
Proof.
intros.
pose proof (IFSAME_B).
rewrite <- IFSAME_B with (b:= (Bvar n)) (b1:=(ifb (ifb (Bvar n) b1 b2 ) b3 b4)).
pose proof(IFEVAL_B).
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with (b1 := (ifb b1 b3 b4))(b2:= (ifb b2 b3 b4)).
simpl.
reflexivity.
Qed.
(**For a function [f: message -> message -> Bool], we have [f(if b then x else y, z , z1) = if b then f(x,z,z1) else f(x,y,z1)] *)
Theorem IFMORPH_M2: forall (n:nat)(b1 b2 :Bool)(y z : message), 
 (ifm (ifb (Bvar n) b1 b2 ) y z)  #(ifm (Bvar n) (ifm  b1  y z ) (ifm  b2 y z) ).
Proof.
intros.
rewrite <- IFSAME_M with (b:=(Bvar n))(x:= ifm (ifb (Bvar n) b1 b2) y z).
rewrite IFEVAL_M.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_M with (t1:=  (ifm b1 y z))(t2:= (ifm b2 y z)).
simpl.
reflexivity.
Qed.

(** For a function [f: Bool -> Bool -> Bool], we have [f(if b then x else y, z) = if b then f(x,z) else f(y,z) ] *)

Theorem IFMORPH_B3: forall  (n n1 n2 n3 :nat), ( eqb (ifb (Bvar n) (Bvar n1) (Bvar n2)) (Bvar n3)) ##  (ifb (Bvar n) (eqb (Bvar n1) (Bvar n3) ) (eqb (Bvar n2) (Bvar n3))).
Proof.
intros.
rewrite <- IFSAME_B with (b:=(Bvar n))( b1:= eqb (ifb (Bvar n) (Bvar n1) (Bvar n2)) (Bvar n3)).
rewrite IFEVAL_B.
simpl. rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFEVAL_B with (b1:= (eqb (Bvar n1) (Bvar n3)))(b2:= (eqb (Bvar n2) (Bvar n3))).
simpl.
reflexivity.
Qed.

Theorem IFMORPH_M3: forall  (n n1 n2 n3 :nat), ( eqm (ifm (Bvar n) (Mvar n1) (Mvar n3))  (ifm (Bvar n) (Mvar n2) (Mvar n3))) ## ( ifb (Bvar n) (eqm (Mvar n1)  (ifm (Bvar n) (Mvar n2) (Mvar n3) )) (eqm (Mvar n3)  (ifm (Bvar n) (Mvar n2) (Mvar n3)))). 
Proof.
intros.
rewrite <- IFSAME_B with (b:=(Bvar n))( b1:= eqm (ifm (Bvar n) (Mvar n1) (Mvar n3))  (ifm (Bvar n) (Mvar n2) (Mvar n3))).
rewrite IFEVAL_B.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M .
rewrite IFTRUE_M.
rewrite IFFALSE_M.
rewrite IFEVAL_B with (b1:= (eqm (Mvar n1) (ifm (Bvar n) (Mvar n2) (Mvar n3))))(b2:= (eqm (Mvar n3) (ifm (Bvar n) (Mvar n2) (Mvar n3)))).
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
reflexivity.
Qed.

Theorem IFMORPH_M5 : forall (n1 n2 n3 :nat) (m1 m2 m3 m4: message),  (ifm (Bvar n1) (ifm (Bvar n2) m1 m2 ) (ifm (Bvar n3) m3 m4)) # (ifm (Bvar n2) (ifm (Bvar n1) m1 (ifm (Bvar n3) m3 m4)) (ifm (Bvar n1) m2 (ifm (Bvar n3) m3 m4))).
Proof. intros. 
pose proof(IFSAME_M (Bvar n2) (ifm (Bvar n1) (ifm (Bvar n2) m1 m2 ) (ifm (Bvar n3) m3 m4))).
rewrite IFEVAL_M with (n:= n2) (t1:= (ifm (Bvar n1) (ifm (Bvar n2) m1 m2 ) (ifm (Bvar n3) m3 m4))) (t2 := (ifm (Bvar n1) (ifm (Bvar n2) m1 m2 ) (ifm (Bvar n3) m3 m4))) in H.
simpl in H.
repeat rewrite <- beq_nat_refl in H.
rewrite <-H. 
rewrite IFEVAL_M with (n:= n2) (t1:= (ifm (Bvar n1) m1 (ifm (Bvar n3) m3 m4))) (t2 := (ifm (Bvar n1) m2 (ifm (Bvar n3) m3 m4))).
simpl. rewrite  IFTRUE_M, IFFALSE_M.
reflexivity. Qed.

Theorem IFMORPH_M6 : forall(n1 n2 :nat) (m1 m2 m3:message), (ifm (Bvar n1) m1 (ifm (Bvar n2) m2 m3)) # (ifm (Bvar n2) (ifm (Bvar n1) m1 m2) (ifm (Bvar n1)  m1 m3)).
Proof. intros. pose proof(IFSAME_M (Bvar n2)  (ifm (Bvar n1) m1 (ifm (Bvar n2) m2 m3))).
rewrite IFEVAL_M in H.
simpl in H. repeat rewrite <- beq_nat_refl in H.
rewrite  IFTRUE_M, IFFALSE_M in H.
rewrite <-H. clear H.
rewrite IFEVAL_M with (t1:= (ifm (Bvar n1) m1 m2)).
simpl. reflexivity. Qed.
(*
Axiom IFMORPH_B4: forall  (n1:nat) (b1 b2 b3:Bool), (ifb (Bvar n1) b1 (ifb (Bvar (n1+1)) b2 b3))  ## (ifb (Bvar (n1+1)) (ifb (Bvar n1) b1 b2) (ifb (Bvar n1) b1 b3)) .
*)

Theorem IFMORPH_M4 : forall (n1:nat) (m1 m2 m3 : message), (ifm (Bvar n1) m1 (ifm (Bvar (n1+1)) m2 m3) ) # (ifm (Bvar (n1+1)) (ifm (Bvar n1) m1 m2)(ifm (Bvar n1) m1 m3)).
Proof. 
intros.
rewrite <- IFSAME_M with (b:= (Bvar (n1+1))) (x:= (ifm (Bvar n1)  m1 (ifm (Bvar (n1+1)) m2 m3))).
rewrite IFEVAL_M.
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_M.
rewrite IFFALSE_M.
assert(H: beq_nat n1 (n1 +1) = false).
induction n1.
simpl.  reflexivity.
simpl. 
rewrite IHn1. 
reflexivity. 
rewrite H.
 rewrite IFEVAL_M with (t1:=(ifm (Bvar n1) m1 m2) )(t2:= (ifm (Bvar n1) m1 m3) ).
simpl.
rewrite H.
reflexivity.
Qed.
