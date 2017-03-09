
Load "extra_theorems". 
(*******************tactics *************************)
(**************************application **************************)
Ltac redg := try rewrite IFTRUE_M ; try rewrite IFFALSE_M ; try rewrite IFSAME_M ;try rewrite IFTRUE_B ; try rewrite IFFALSE_B ; try rewrite IFSAME_B; try rewrite IFTFb.

Ltac red_in H:= try rewrite IFTRUE_M in H; try rewrite IFFALSE_M in H; try rewrite IFSAME_M in H;try rewrite IFTRUE_B in H; try rewrite IFFALSE_B in H; try rewrite IFSAME_B in H; try rewrite IFTFb in H.

(************rewrite hypothesis************)

Ltac rew_clear H := rewrite H ; simpl; clear H.
Ltac rew_clear_in H H1:= rewrite H in H1; simpl in  H1 ;clear H .
(*****************************Forall elimination ***************************)
Ltac fall_elm_in n1 b1 H := try apply Forall_ELM_EVAL_B with (n:= n1) (b:= b1) in H;  try apply Forall_ELM_EVAL_M with (n:= n1) (x:= b1) in H; simpl in H; try rewrite H.
 

Ltac fall_elm n1 b1  :=  try apply Forall_ELM_EVAL_B with (n:= n1) (b:= b1) ;  try apply Forall_ELM_EVAL_M with (n:= n1) (x:= b1) ;  simpl.



(*******************& elimination *******************)
Ltac andB_elm_msg n1 t1 t2  := pose proof( mor_eval_andB n1 t1 t2) ;
match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ; match goal with | [H : ?X # ?Y |- _ ] =>   rewrite H; clear H end
         
 end.

Ltac andB_elm_msg_in n1 t1 t2 H1 := pose proof( mor_eval_andB n1 t1 t2) ;
match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ; rewrite H in H1; clear H 
         
 end.




Ltac rew_andB_elm_msg :=
repeat match goal with 
|[H: _ |-  context [(if_then_else_M  ((Bvar ?n2) & ?P) ?X ?Y )] ] => andB_elm_msg n2 X Y 
end.



Ltac rew_andB_elm_in_msg H1 := 
repeat match goal with
 |[H: context [(if_then_else_M ((Bvar ?n2) & ?P) ?X ?Y )] |- _ ] =>  andB_elm_msg_in n2 X Y H1 end.


(***********************not sure if we require them*****)


Ltac andB_elm_bol n1 t1 t2  := pose proof( mor_eval_andB n1 t1 t2) ;
match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ;  match goal with | [H : ?X # ?Y |- _ ] =>   rewrite H; clear H end
          
 end.

Ltac  andB_elm_bol_in n1 t1 t2 H1  := pose proof( mor_eval_andB n1 t1 t2) ;
match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ;    rewrite H in H1; clear H 
           
 end.

Ltac rew_andB_elm_bol :=
repeat match goal with 
|[H: _ |-  context [(if_then_else_B ((Bvar ?n2) & ?P) ?X ?Y )] ] => andB_elm_bol  n2 X Y 
end.


Ltac rew_andB_elm_in_bol H1 := 
repeat match goal with
 |[H: context [(if_then_else_B ((Bvar ?n2) & ?P) ?X ?Y )] |- _ ] =>  andB_elm_bol_in n2 X Y H1 end.

(******************************************IFTF***********************************)



Ltac rew_IFTF b  := pose proof(IFTFb b); 
 match goal with
| [H : _ |- ?X ## ?Y ] =>  rewrite H ; clear H; simpl
 end.

Ltac rew_IFTF_in b H1  := pose proof(IFTFb b);
match goal with
  | [H : ?X ## ?Y |- _ ] =>   rewrite H in H1 ; clear H; simpl in H1
                             
 end.



Ltac rew_IFTF_all_in H1  := 
repeat match goal with 
|[ H : context [  (if_then_else_B ?X TRue FAlse)]   |- _ ] => rew_IFTF_in X H1 
end. 



Ltac rew_IFTF_all  := 
repeat match goal with 
|[ H : _ |-  context [ if_then_else_B ?X TRue FAlse ]  ] => rew_IFTF X 
end. 




(*************IFMORPH*****message_bool*******)

Ltac ifmor_msg_bol n1 b1 b2 t1 t2  := pose proof(IFMORPH_M2 n1 b1 b2 t1 t2);

match goal with
| [H : _ |-  ?X # ?Y ] =>    simpl in H ; match goal with | [H : ?X # ?Y |- _ ] =>   rewrite H; clear H end
         
 end.
Ltac ifmor_msg_bol_in n1 b1 b2 t1 t2 H1 := pose proof(IFMORPH_M2 n1 b1 b2 t1 t2);

match goal with
| [H : ?X # ?Y |- _ ] =>    simpl in H ; match goal with | [H : ?X # ?Y |- _ ] =>   rewrite H in H1; clear H end
         
 end.


Ltac rew_ifmor_msg_bol :=
repeat match goal with 
|[ H : _ |-  context [ if_then_else_M (if_then_else_B (Bvar ?n1) ?Y ?Z) ?P ?Q]  ] => ifmor_msg_bol n1 Y Z P Q
end. 

Ltac rew_ifmor_msg_bol_in H1 :=
repeat match goal with 
|[ H : context [ if_then_else_M (if_then_else_B (Bvar ?n1) ?Y ?Z) ?P ?Q]   |- _ ] => ifmor_msg_bol_in n1 Y Z P Q H1
end. 


(********************IFMRPH***********Bool_Bool_fst*****************)

Ltac ifmor_bol_bol_fst n1 b1 b2 b3 b4  := pose proof(IFMORPH_B2 n1 b1 b2 b3 b4);
match goal with
| [H :_ |-  ?X ## ?Y ] =>    simpl in H ; match goal with | [H : ?X ## ?Y |- _ ] =>   rewrite H; clear H end
         
 end.
Ltac ifmor_bol_bol_fst_in  n1 b1 b2 b3 b4 H1 := pose proof(IFMORPH_B2 n1 b1 b2 b3 b4);
match goal with
| [H : ?X ## ?Y |- _ ] =>    simpl in H ; match goal with | [H : ?X ## ?Y |- _ ] =>   rewrite H in H1; clear H end
   
 end.


Ltac rew_ifmor_bol_bol_fst :=
repeat match goal with 
|[ H : _ |-  context [ if_then_else_B (if_then_else_B (Bvar ?n1) ?Y ?Z) ?P ?Q]  ] =>  ifmor_bol_bol_fst n1 Y Z P Q
end. 

Ltac rew_ifmor_bol_bol_in_fst H1 :=
repeat match goal with 
|[ H : context [ if_then_else_B (if_then_else_B (Bvar ?n1) ?Y ?Z) ?P ?Q]   |- _ ] =>  ifmor_bol_bol_fst_in n1 Y Z P Q H1
end. 


(********************IFMRPH***********Bool_Bool_snd*****************)

Ltac ifmor_bol_bol_snd n1 n2 b1 b2 b3  := pose proof(IFMORPH_B1 n1 n2 b1 b2 b3 );
match goal with
| [H : _ |- ?X ## ?Y ] =>    simpl in H ; match goal with | [H : ?X ## ?Y |- _ ] =>   rewrite H; clear H end
         
 end.
Ltac ifmor_bol_bol_snd_in  n1 n2 b1 b2 b3  H1 := pose proof(IFMORPH_B1 n1 n2 b1 b2 b3 );
match goal with
| [H : ?X ## ?Y |- _ ] =>    simpl in H ; match goal with | [H : ?X ## ?Y |- _ ] =>   rewrite H in H1; clear H end
   
 end.


Ltac rew_ifmor_bol_bol_snd :=
repeat match goal with 
|[ H : _ |-  context [ if_then_else_B (Bvar ?n1) (if_then_else_B (Bvar ?n2) ?B1 ?B2) ?B3 ]  ] =>  ifmor_bol_bol_snd n1 n2 B1 B2 B3
end. 

Ltac rew_ifmor_bol_bol_in_snd H1 :=
repeat match goal with 
|[ H : context [ (if_then_else_B (Bvar ?n1) (if_then_else_B (Bvar ?n2) ?B1 ?B2) ?B3)]   |- _ ] =>  ifmor_bol_bol_snd_in n1 n2 B1 B2 B3 H1
end. 



(**************************************recent***************Testing************)
  
(**********************************tactics to apply if b is same on both sides**********)


Ltac aply_breq :=
match goal with
| [|- (if_then_else_M ?B ?X1 ?Y1) # (if_then_else_M ?B ?X2 ?Y2) ] =>  apply breq_msgeq'; simpl; redg; try reflexivity

end.

Ltac aply_breq_same :=
match goal with
| [|- (if_then_else_M ?B ?X ?Y1) # (if_then_else_M ?B ?X ?Y2) ] =>  apply breq_msgeq1'; simpl
 
end.

(********************************three sessions 1 2 3 *************************)
(******************tactics to make (to x) = j is false if (to x) = i is true where i <> j *********)
Ltac false_to_sesns n  := 
match goal with 
| [|- (if_then_else_M (EQ_M ?X (i ?N)) ?X1 ?Y1) #  (if_then_else_M (EQ_M ?X (i ?N)) ?X2 ?Y2) ] => assert (beq_nat N n =false) ; try reflexivity ;
match goal with 
| [H: beq_nat ?N ?N2 = false |- _ ] => 
  apply IFEVAL_M''' with (x:= X ) (n1:= N) (n2:= N2) (t1 := X1) (t2:= Y1) in H; rewrite H; clear H end; assert (beq_nat N n =false) ; try reflexivity ;
match goal with 
| [H: beq_nat ?N ?N2 = false |- _ ] => 
  apply IFEVAL_M''' with (x:= X ) (n1:= N) (n2:= N2) (t1 := X2) (t2:= Y2) in H; rewrite H; clear H end

end.

Ltac  false_to_sesns_all := try false_to_sesns 1; try false_to_sesns 2; try false_to_sesns 3.

(******************************************************************************)



(*************apply andB elm ****************)


Ltac aply_andB_elm := 

match goal with 
|[|- context[if_then_else_M (if_then_else_B ?B1 ?B2 FAlse) ?T1 ?T2 ] ] => rewrite andB_elm' with (b1:= B1) (b2:= B2) (x:= T1) (y:= T2)
end.


