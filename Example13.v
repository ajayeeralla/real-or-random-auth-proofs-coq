Load "EQBRANCH".

         
(*******************************************)
Theorem Ex13bol:  (EQ_B  TRue FAlse) ##  FAlse.
Proof.

assert(H : (Bvar 1) ##  (if_then_else_B (Bvar 1) TRue FAlse) ) .
rewrite IFTF with (n :=1) . reflexivity.
apply Forall_ELM_EVAL_B with (n:=1)(b:= (EQ_B  TRue FAlse)) in H .
simpl in H.
assert(H1 : (if_then_else_B (EQ_B  (Bvar 1)  (Bvar 2))[3 := (Bvar 1)](Bvar 3) FAlse) ## (if_then_else_B (EQ_B  (Bvar 1)(Bvar 2)) [3 := (Bvar 2)](Bvar 3)  FAlse)).
rewrite EQ_BRbol_bol with (n1:= 1) (n2:= 2)(b2:=FAlse)(b1:=(Bvar 3)).
reflexivity.
simpl in H1.
apply Forall_ELM_EVAL_B with (n:=1)(b:= TRue) in H1 .
simpl in H1.
apply Forall_ELM_EVAL_B with (n:=2)(b:= FAlse) in H1 .
simpl in H1.

rewrite H1 in H.
rewrite IFSAME_B in H. apply H.
Qed.
(***
Theorem Ex13msg:  (EQ_M  O  (N 1)) ##  FAlse.
Proof.
assert(H : (Bvar 1) ##  (if_then_else_B (Bvar 1) TRue FAlse) ) .
rewrite IFTF with (n :=1) . reflexivity.
apply Forall_ELM_EVAL_B with (n:=1)(b:= (EQ_M  O (N 1))) in H .
simpl in H.
assert(H1 : (if_then_else_B (EQ_M  (Mvar 1)  (Mvar 2))[[3 := (Mvar 1)]](Bvar 3) FAlse) ## (if_then_else_B (EQ_M  (Mvar 1)(Mvar 2)) [[3 := (Mvar 2)]](Bvar 3)  FAlse)).
rewrite EQ_BRmsg_bol with (n1:= 1) (n2:= 2)(b2:=FAlse)(b1:=(Bvar 3)).
reflexivity.
simpl in H1.
apply Forall_ELM_EVAL_B1 with (n:=1)(b:= O) in H1 .
simpl in H1.
apply Forall_ELM_EVAL_B1 with (n:=2)(b:= (N 1)) in H1 .
simpl in H1.

rewrite H1 in H.
rewrite IFSAME_B in H. apply H.
Qed.**)