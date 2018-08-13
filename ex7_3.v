
(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                   University of Missouri-Columbia.                   *)
(*                                                                      *)
(*                                                                      *)
(*                                                                      *)
(************************************************************************)

Load "cor_ex7_2".

(** This library defines a theorem that states, 

[if EQ(x1 , x2) then x1 else y = if EQ(x1 ,x2) then x2 else y] *)

Theorem Example11_M:   (ifm (eqm  (Mvar 1) (Mvar 2)) (Mvar 1) (Mvar 3)) # (ifm (eqm  (Mvar 1) (Mvar 2)) (Mvar 2) (Mvar 3)) .
Proof.
intros.
rewrite EQmsg .
(assert(H1:  (eqm (ifm (Bvar 0) (Mvar 1) (Mvar 3) ) (ifm (Bvar 0) (Mvar 2) (Mvar 3) )) ## (ifb (Bvar 0) (eqm  (Mvar 1) (ifm (Bvar 0) (Mvar 2) (Mvar 3) ))  (eqm  (Mvar 3) (ifm (Bvar 0) (Mvar 2) (Mvar 3) ))))).
apply IFMORPH_M3 with (n:=0) (n1:=1)(n2:=2)(n3:=3)  .
apply Forall_ELM_EVAL_B  with (n:=0) (b:= (eqm (Mvar 1) (Mvar 2))) in H1.
simpl in H1.
assert (H2: (ifb (Bvar 0)
    [[4 := ifm (Bvar 0) (Mvar 2) (Mvar 3)]](eqm (Mvar 1) (Mvar 4))
    [[4 := ifm (Bvar 0) (Mvar 2) (Mvar 3)]](eqm (Mvar 3) (Mvar 4))) ##
  ( ifb (Bvar 0) [[4 := Mvar 2]](eqm (Mvar 1) (Mvar 4))
    [[4 := Mvar 3]](eqm (Mvar 3) (Mvar 4))) ).
apply Ex9msg_bol1 with (b:= (Bvar 0))(n1:=2)(n2:=3)(n3:=2)(n4:=3)(n5:=4)(n6:= 4) (b1:= (eqm (Mvar 1) (Mvar 4))) (b2:= (eqm (Mvar 3) (Mvar 4))) .
simpl in H2.
apply Forall_ELM_EVAL_B  with (n:=0) (b:= (eqm (Mvar 1) (Mvar 2))) in H2.
simpl in H2.
rewrite H2 in H1 .
rewrite H1.
assert (H3:   (eqm (Mvar 3) (Mvar 3)) ##   TRue).
apply EQmsg with (x:=(Mvar 3))( y:= (Mvar 3)).
reflexivity. 
rewrite H3.
assert (H4: (ifb (Bvar 0) TRue FAlse) ## (Bvar 0)).
apply IFTF with (n:=0).
apply Forall_ELM_EVAL_B2 with (n :=0)(b:= (eqm (Mvar 1) (Mvar 2))) in H4.
simpl  in H4.
assert(H6:  (ifb (Bvar 0) (Bvar 0) TRue) ## (ifb (Bvar 0) TRue TRue)).
apply IFEVAL_B with (n:=0) (b1:=(Bvar 0)) (b2:= TRue) .
apply Forall_ELM_EVAL_B with (n :=0)(b:= (eqm (Mvar 1) (Mvar 2))) in H6.
simpl  in H6.
rewrite H6.
apply IFSAME_B.
Qed.

Theorem Example11_B:    (ifb (eqb  (Bvar 1) (Bvar 2)) (Bvar 1) (Bvar 3)) ## ( ifb (eqb  (Bvar 1) (Bvar 2)) (Bvar 2) (Bvar 3) ).
Proof.
intros.
rewrite EQ_Bool .
(assert(H1:  (eqb (ifb (Bvar 0) (Bvar 1) (Bvar 3) ) (ifb (Bvar 0) (Bvar 2) (Bvar 3) )) ## (ifb (Bvar 0) (eqb  (Bvar 1) (ifb (Bvar 0) (Bvar 2) (Bvar 3) ))  (eqb  (Bvar 3) (ifb (Bvar 0) (Bvar 2) (Bvar 3) ))))).
assert (H2 : (eqb (ifb (Bvar 0) (Bvar 1) (Bvar  3)) (Bvar 4)) ## ( ifb (Bvar 0) (eqb (Bvar 1) (Bvar 4) ) (eqb (Bvar 3) (Bvar 4)))).
apply IFMORPH_B3 with  (n:=0) (n1:=1).
apply Forall_ELM_EVAL_B  with (n:=4) (b:= ifb (Bvar 0) (Bvar 2) (Bvar 3) )in H2.
simpl in H2.
apply H2.
apply Forall_ELM_EVAL_B  with (n:=0) (b:= (eqb (Bvar 1) (Bvar 2))) in H1.
simpl in H1.
assert (H2:  (ifb (Bvar 0) (eqb (Bvar 1) (ifb (Bvar 0) (Bvar 2) (Bvar 3) ) )   (eqb (Bvar 3) (ifb (Bvar 0) (Bvar 2) (Bvar 3) ) )) ## (ifb (Bvar 0) (eqb (Bvar 1) (Bvar 2) ) ( eqb (Bvar 3) (Bvar 3))  )).
apply Ex9bol_bol1 with (n1:=2)(n2:=3)(n3:=2)(n4:=3)(n5:=4)(n6:= 4) (b1:= (eqb (Bvar 1) (Bvar 4))) (b2:= (eqb (Bvar 3) (Bvar 4))) .
apply Forall_ELM_EVAL_B  with (n:=0) (b:= (eqb (Bvar 1) (Bvar 2))) in H2.
simpl in H2.
rewrite H1 .
rewrite H2.
assert (H3:   (eqb (Bvar 3) (Bvar 3)) ## TRue).
apply EQ_Bool with (x:=(Bvar 3))( y:= (Bvar 3)).
reflexivity.
rewrite H3. 
assert (H4: (ifb (Bvar 0) TRue FAlse) ## (Bvar 0)).
apply IFTF with (n:=0).
apply Forall_ELM_EVAL_B2 with (n :=0)(b:= (eqb (Bvar 1) (Bvar 2))) in H4.
simpl  in H4.
assert(H6: (ifb (Bvar 0) (Bvar 0) TRue) ## ( ifb (Bvar 0) TRue TRue)).
apply IFEVAL_B with (n:=0) (b1:=(Bvar 0)) (b2:= TRue) .
apply Forall_ELM_EVAL_B with (n :=0)(b:= (eqb (Bvar 1) (Bvar 2))) in H6.
simpl  in H6.
rewrite H6.
apply IFSAME_B.
Qed.

Axiom Example11_B1: forall (n1 n2 n3 :nat), (ifb (eqb  (Bvar n1) (Bvar n2)) (Bvar n1) (Bvar n3))  ## ( ifb (eqb  (Bvar n1) (Bvar n2)) (Bvar n2) (Bvar n3)).
Axiom Example11_B2: forall (n1 n2 n3 :nat),  (ifb (eqm  (Mvar n1) (Mvar n2)) (Bvar n1) (Bvar n3))  ## (ifb (eqm  (Mvar n1) (Mvar n2)) (Bvar n2) (Bvar n3)).
Axiom Example11_M1:forall(n1 n2 n3:nat),   (ifm (eqm  (Mvar n1) (Mvar n2)) (Mvar n1) (Mvar n3) ) # (ifm (eqm  (Mvar n1) (Mvar n2)) (Mvar n2) (Mvar n3)).
Axiom Example11_M2:forall(n1 n2 n3:nat),   (ifm (eqb  (Bvar n1) (Bvar n2)) (Mvar n1) (Mvar n3) ) # (ifm (eqb  (Bvar n1) (Bvar n2)) (Mvar n2) (Mvar n3)).
