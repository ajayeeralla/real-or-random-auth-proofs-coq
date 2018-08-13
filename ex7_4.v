(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                   University of Missouri-Columbia.                   *)
(*                                                                      *)
(*                                                                      *)
(*                                                                      *)
(************************************************************************)

Load "ex7_3".
(** This library defines a theorem which states that,

[if b then x1 else y1 = if b then x2 else y2 -> if b then t[[x1]] else t'[[y1]] = if b then t[[x2]] else t'[[y2]] ] *)

Theorem Ex12bol_bol: forall (n1 n2 n3 n4 n5 n6 : nat)(b b1 b2:Bool),   (ifb b (Bvar n1) (Bvar n2)) ## (ifb b (Bvar n3) (Bvar n4)) ->  (ifb b [n5:= (Bvar n1)]b1 [n6:= (Bvar n2)]b2)  ##  (ifb b [n5:= (Bvar n3)]b1  [n6:= (Bvar n4)] b2).
Proof.
intros. 
assert (H1:   (ifb b [n5:= ifb b (Bvar n1) (Bvar n2)] b1 [n6 := ifb b (Bvar n1) (Bvar n2)] b2) ## (ifb b [n5:= (Bvar n1)]b1 [n6:= (Bvar n2)]b2)).
apply Ex9bol_bol1 with  (b1:=b1)(b2:=b2).
rewrite <- H1.
rewrite H.
apply Ex9bol_bol1 with (b1:= b1)(b2:=b2).
Qed.

Theorem Ex12bol_msg: forall (n1 n2 n3 n4 n5 n6 : nat)(b :Bool) (m1 m2 : message),   (ifb b (Bvar n1) (Bvar n2)) ## (ifb b (Bvar n3) (Bvar n4)) ->  (ifm b ((n5:= (Bvar n1))m1) ((n6:= (Bvar n2)) m2))  #  (ifm b ((n5:= (Bvar n3))m1)  ((n6:= (Bvar n4)) m2)).
Proof.
intros. 
pose proof Ex9bol_msg1.
assert (H1:   (ifm b ((n5:= ifb b (Bvar n1) (Bvar n2)) m1) ((n6 := ifb b (Bvar n1) (Bvar n2)) m2)) # (ifm b ((n5:= (Bvar n1))m1) ((n6:= (Bvar n2))m2))).
apply Ex9bol_msg1 with  (m1:=m1)(m2:=m2).
rewrite <- H1.
rewrite H.
apply Ex9bol_msg1.
Qed.

Theorem Ex12msg_msg: forall (n1 n2 n3 n4 n5 n6 : nat)(b:Bool)(m1 m2: message),  (ifm b (Mvar n1) (Mvar n2)) # (ifm b (Mvar n3) (Mvar n4)) ->  ( ifm b (submsg_msg n5 (Mvar n1) m1)  (submsg_msg n6 (Mvar n2) m2))  # (ifm b (submsg_msg n5 (Mvar n3) m1)  (submsg_msg n6 (Mvar n4) m2)).
Proof.
intros. 
assert (H1:  (ifm b (submsg_msg n5  (ifm b (Mvar n1) (Mvar n2)) m1) (submsg_msg n6 (ifm b (Mvar n1) (Mvar n2)) m2)) # ( ifm b (submsg_msg n5  (Mvar n1)  m1) (submsg_msg n6 (Mvar n2) m2))).
apply Ex9msg_msg1 .
rewrite <-H1.
rewrite H. 
apply Ex9msg_msg1.
Qed.

Theorem Ex12msg_bol: forall (n1 n2 n3 n4 n5 n6 : nat)(b:Bool)(b1 b2: Bool),  (ifm b (Mvar n1) (Mvar n2)) # (ifm b (Mvar n3) (Mvar n4)) ->  ( ifb b  ([[ n5 := (Mvar n1)]] b1)  ( [[ n6 := (Mvar n2)]] b2)) ## (ifb b ([[ n5 := (Mvar n3)]] b1)  ([[ n6 := (Mvar n4)]] b2)).
Proof.
intros. 
assert (H1:  (ifb b ( [[ n5 := (ifm b (Mvar n1) (Mvar n2) )]] b1) ([[ n6 := (ifm b (Mvar n1) (Mvar n2))]] b2)) ## ( ifb b ( [[ n5 :=  (Mvar n1)]]  b1) ( [[ n6 :=  (Mvar n2)]] b2))).
apply Ex9msg_bol1 .
rewrite <-H1.
rewrite H. 
apply Ex9msg_bol1.
Qed.
