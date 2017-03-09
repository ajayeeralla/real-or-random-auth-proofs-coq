Load "Example20".

(*****************************************some theorems**********************************************************)
(**************************************************************************************************)

Theorem mor_eval_andB : forall (n1 : nat) (t1 t2:message), (if_then_else_M (Bvar n1)& (Bvar (n1+1)) t1 t2) #
(if_then_else_M (Bvar n1) (if_then_else_M (Bvar (n1+1)) ((n1+1):=TRue)((n1:=TRue)t1) ((n1+1):=FAlse)((n1:=TRue)t2)) (((n1:=FAlse)t2))).

Proof. intros.
unfold andB.
rewrite <- IFSAME_M with (b:= (Bvar n1)) (x:=  (if_then_else_M (if_then_else_B (Bvar n1) (Bvar (n1+1)) FAlse) t1 t2)) .
rewrite IFEVAL_M .
simpl.
rewrite <- beq_nat_refl.
rewrite IFTRUE_B.
rewrite IFFALSE_B.
rewrite IFFALSE_M.
assert(H: (beq_nat (n1+1) n1 = false)).
rewrite Nat.eqb_sym.
induction n1.
reflexivity.
simpl. auto.
rewrite H.
rewrite IFEVAL_M with (n:= (n1+1)).
reflexivity.
Qed.

(***************corollary*********************************************)
Axiom mor_eval_andB' : forall (b1 b2 : Bool) (t1 t2 : message) , (if_then_else_M b1 & b2 t1 t2 ) # (if_then_else_M b1 (if_then_else_M b2 (subbol_msg' b2 TRue (subbol_msg' b1 TRue t1))  (subbol_msg' b2 FAlse (subbol_msg' b1 TRue t2))) (subbol_msg' b1 FAlse t2)).


Theorem breq_msgeq: forall (n:nat) (m1 m2 m3 m4 :message) , ((n:= TRue)m1)# ((n:= TRue)m3) -> ((n:= FAlse)m2)# ((n:= FAlse)m4) -> (if_then_else_M (Bvar n) m1 m2) # (if_then_else_M (Bvar n) m3 m4).
Proof. intros.
rewrite IFEVAL_M. rewrite H. rewrite H0. rewrite IFEVAL_M with (t1:= m3) (t2:= m4).
reflexivity. Qed.

(*****************Corollary ***********************************************)
Theorem breq_msgeq': forall (  b :Bool) (m1  m2 m3 m4 :message) ,  (subbol_msg' b TRue m1) # (subbol_msg' b TRue m2) -> (subbol_msg' b FAlse m3) # (subbol_msg' b FAlse m4) -> (if_then_else_M b m1 m3) # (if_then_else_M b m2 m4).

Proof. intros.
rewrite IFEVAL_M'.
rewrite IFEVAL_M' with (t1:= m2).
rewrite H, H0.
reflexivity.
Qed.
(************using (Bvar n)*****************)
Theorem breq_msgeq'': forall (n:nat) (m1  m2 m3 m4 :message) ,  (subbol_msg n TRue m1) # (subbol_msg n TRue m2) -> (subbol_msg n FAlse m3) # (subbol_msg n FAlse m4) -> (if_then_else_M (Bvar n) m1 m3) # (if_then_else_M (Bvar n) m2 m4).

Proof. intros.

rewrite IFEVAL_M.
rewrite IFEVAL_M with (t1:= m2).
rewrite H, H0.
reflexivity.
Qed.

Axiom breq_msgeq''': forall (n:nat) (b:Bool) (m1  m2 m3 m4 :message) ,  (if_then_else_M (Bvar n) m1 m3) # (if_then_else_M (Bvar n) m2 m4) ->   (if_then_else_M b m1 m3) # (if_then_else_M b m2 m4).
(***Proof.
 intros.

apply Forall_ELM_EVAL_M with (n:=n) (x:=b) in H.
simpl in H. rewrite <- beq_nat_refl in H. ***)
(****************************** then branches are equal******************)
Axiom breq_msgeq1: forall (n:nat) ( m2 m3 m4 :message) ,  ((n:= FAlse)m2)# ((n:= FAlse)m4) -> (if_then_else_M (Bvar 1) m3 m2) # (if_then_else_M (Bvar n) m3 m4).

 Theorem breq_msgeq1': forall (  b :Bool) ( m2 m3 m4 :message) ,  (subbol_msg' b FAlse m2) # (subbol_msg' b FAlse m4) -> (if_then_else_M b m3 m2) # (if_then_else_M b m3 m4).

Proof. intros . rewrite IFEVAL_M'.
rewrite IFEVAL_M' with (t2:= m4).
rewrite H.
reflexivity.
Qed.

Theorem  andB_elm : forall (n1 n2 : nat) (x y: message), (if_then_else_M (Bvar n1) &  (Bvar n2) x y) # (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2) x y) y).
Proof. intros.
rewrite <- IFSAME_M with (b:= (Bvar n1)) (x:= (if_then_else_M (Bvar n1) & (Bvar n2) x y)) at 1. 
rewrite IFEVAL_M with (n:= n1). simpl. 
rewrite <- beq_nat_refl.
Eval compute in subbol_msg' (Bvar n1) TRue x.

rewrite IFEVAL_M with (n:= n1) (t2:= y).
simpl.
 rewrite IFTRUE_B, IFFALSE_B, IFFALSE_M.

reflexivity .

Qed.

Axiom andB_elm': forall (b1 b2: Bool) (x y : message), (if_then_else_M b1& b2 x y) #  (if_then_else_M b1 (if_then_else_M b2 x y ) y).
(**
Proof. intros.
pose proof (andB_elm 0 1 x y).
apply Forall_ELM_EVAL_M with (x:= b1) (n:=0) in H. simpl in H.
apply Forall_ELM_EVAL_M with (x:= b2) (n:=1) in H. simpl in H.
Check message_ind.
Scheme message_mut := Induction for message Sort Prop
with Bool_mut := Induction for Bool Sort Prop.
Check message_mut.

Check message_ind.
Check Bool_mut.
assert ([1 := b2](b1) ## b1).
(**apply (message_mut (fun m : Bool => forall b: Bool, 
         (subbol_bol 1 m b) ## b)
    (fun m1 : Bool => forall b1 : Bool, 
            (subbol_bol 1 m1 b1) ## b1)). 
apply ( Bool_mut (fun m : message => forall b: Bool, 
         (submsg_bol 1 m b) ## b)
    (fun m1 : Bool => forall b1 : Bool, 
            (subbol_bol 1 m1 b1) ## b1)). 
**)
Admitted.
**)

Theorem  breq_msgeq_andB : forall (n1 n2:nat) (m1 m2 m1' m2' :message), ( (n1 := TRue) (n2 := TRue) m1) #  ((n1 := TRue) (n2 := TRue) m1') ->  ( (n1 := TRue) (n2 := FAlse) m2) #
 ( (n1 := TRue) (n2 := FAlse) m2') -> ((n1 := FAlse) m2) #  ((n1 := FAlse) m2') -> (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2) m1 m2) m2) #  (if_then_else_M (Bvar n1) (if_then_else_M (Bvar n2) m1' m2') m2').
 Proof. intros.  rewrite IFEVAL_M with (t1:= m1) (t2:= m2). rewrite IFEVAL_M with (t2:= m2).
simpl. rewrite IFEVAL_M with (t1:= m1') (t2:= m2'). rewrite IFEVAL_M with (t2:= m2').
simpl. rewrite H; rewrite H0 ; rewrite H1. reflexivity. Qed.


(*******************************************************************)



Check message_ind. 
Scheme message_mut := Induction for message Sort Prop
with Bool_mut := Induction for Bool Sort Prop.
Check message_mut.
Axiom sub_invar: forall (t:message)  (b:Bool), (subbol_msg' b b t) # t. 
(**Proof.  apply (message_mut (fun t: message => forall b:Bool, (subbol_msg' b b t) # t) (fun B:Bool => forall M:message ,
(subbol_msg' B B M) # M)). 
Check Bool_mut.
induction n. 
intros. simpl. reflexivity.
intros.  
simpl. reflexivity. 
reflexivity. reflexivity.  intros. simpl . reflexivity.   intros.  simpl.  apply H1.
induction n. intros. 
simpl.  reflexivity. 
simpl. 
apply nat_ind.
 apply (Bool_mut (fun M1: message => forall b:Bool, (subbol_msg' b b M1) # M1) (fun B:Bool => forall M:message ,
(subbol_msg' B B M) # M)). 

intros. 
simpl. reflexivity. 
apply Bool_ind.  

induction t. 
induction b. repeat ( simpl;  reflexivity);simpl. 
t *)
Axiom sub_in_sub: forall (b1 b2 b3 b4:Bool) (t:message), (**(occbol_in_msg b1 t = false) ->**) (subbol_msg' b1 b2 (subbol_msg' b3 b4 t)) # (subbol_msg' b3 (subbol_bol' b1 b2 b4) t).
(*Axiom sub_msg_sub: forall (n:nat) (b1 b2 : Bool) (x t:message), {{ n:= x}} (subbol_msg' b1 b2 t) # (subbol_msg' (submsg_bol n x b1) (submsg_bol n x b2) (submsg_msg n x t)). *)
Axiom dist_sesns_neq: forall (n1 n2:nat), (beq_nat n1 n2) =false  ->  (EQ_M (i n1) (i n2)) ##  FAlse.

Theorem dist_sesns_false: forall (n1 n2:nat),  (beq_nat n1 n2 = false) ->  (EQ_M (Mvar 1) (i n1)) & (EQ_M (Mvar 1) (i n2)) ## FAlse. 
Proof.  intros. 
unfold andB.
pose proof( EQ_BRmsg_msg''  (Mvar 1) (Mvar 1)  (i n1)    (EQ_M (Mvar 1) (i n2))  FAlse).
simpl in H0.
rewrite H0. 
apply dist_sesns_neq in H.
rewrite H. 
rewrite IFSAME_B. 
 reflexivity. 

Qed.

Theorem dist_sesns_false' : forall (n1 n2:nat) (x:message) , (beq_nat n1 n2 = false) ->  (EQ_M x (i n1)) & (EQ_M x (i n2)) ## FAlse .
Proof . 
intros. 
apply dist_sesns_false in H.
apply Forall_ELM_EVAL_B1 with (n:= 1) (b:= x) in H. simpl in H. assumption. Qed.



Theorem IFEVAL_M'': forall (n1 n2: nat) ( t1 t2:message), (beq_nat n1 n2 = false) -> (if_then_else_M  (EQ_M (Mvar 1) (i n1)) t1 t2) # (if_then_else_M  (EQ_M (Mvar 1) (i n1)) (subbol_msg' (EQ_M (Mvar 1) (i n2)) FAlse t1) t2).
Proof. 
intros.

apply dist_sesns_false in H.  
assert( (if_then_else_M (EQ_M (Mvar 1) (i n1)) t1 t2) #  (if_then_else_M (EQ_M (Mvar 1) (i n1)) (subbol_msg' (EQ_M (Mvar 1) (i n2)) (EQ_M (Mvar 1) (i n2)) t1) t2)).

rewrite sub_invar with(b:= (EQ_M (Mvar 1) (i n2))) (t:= t1). reflexivity.
assert( (EQ_M (Mvar 1) (i n2))  ##  (EQ_M (Mvar 1) (i n2)) & TRue).
simpl. unfold andB. rewrite IFTFb. reflexivity.
rewrite H1 in H0 at 2.
assert((if_then_else_M (EQ_M (Mvar 1) (i n1)) 
            (subbol_msg' (EQ_M (Mvar 1) (i n2))
               (EQ_M (Mvar 1) (i n2)) & (TRue) t1) t2) # (if_then_else_M (EQ_M (Mvar 1) (i n1))
            (subbol_msg' (EQ_M (Mvar 1) (i n2))
               (EQ_M (Mvar 1) (i n2)) & (EQ_M (Mvar 1) (i n1))  t1)  t2)).

 rewrite IFEVAL_M' with (t1:=  (subbol_msg' (EQ_M (Mvar 1) (i n2))
           (EQ_M (Mvar 1) (i n2)) & (EQ_M (Mvar 1) (i n1)) t1)).
rewrite IFEVAL_M'.
simpl. 
assert( (subbol_msg' (EQ_M (Mvar 1) (i n1)) TRue
         (subbol_msg' (EQ_M (Mvar 1) (i n2)) (EQ_M (Mvar 1) (i n2)) & (TRue)
            t1)) # (subbol_msg' (EQ_M (Mvar 1) (i n1)) TRue
           (subbol_msg' (EQ_M (Mvar 1) (i n2))
              (EQ_M (Mvar 1) (i n2)) & (EQ_M (Mvar 1) (i n1)) t1))).
repeat rewrite sub_in_sub. 

simpl.  rewrite <- beq_nat_refl. 
SearchAbout beq_nat.
rewrite <- Nat.eqb_sym.
destruct beq_nat. reflexivity.  reflexivity. 

rewrite H2. reflexivity.
rewrite H2 in H0.
rewrite andB_comm in H.
rewrite H in H0.
assumption. 
Qed.
Axiom IFMORPH_M2':  forall  ( b b1 b2 : Bool) (y z : message),
      (if_then_else_M (if_then_else_B b b1 b2) y z)
      # (if_then_else_M b (if_then_else_M b1 y z)
           (if_then_else_M b2 y z)).
Axiom IFEVAL_M''': forall (n1 n2: nat) (x t1 t2:message), beq_nat n1 n2 = false -> (if_then_else_M  (EQ_M x (i n1)) t1 t2) # (if_then_else_M  (EQ_M x (i n1)) (subbol_msg' (EQ_M x (i n2)) FAlse t1) t2).
(*Axiom EQbrmsg_msg'' :forall  ( m m1 m2 m3 m4 :message) ,  (if_then_else_M  (EQ_M m1 m2 )  (submsg_msg' m m1 m3) m4) #  (if_then_else_M (EQ_M m1 m2)   (submsg_msg' m m2 m3) m4).
*)
Axiom andB_elm'':  forall (b1 b2 : Bool) (x y : message),
        (if_then_else_M (if_then_else_B b1 b2 FAlse) x y)
       # (if_then_else_M b1 (if_then_else_M b2 x y) y).
