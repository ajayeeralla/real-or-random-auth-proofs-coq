Load "tactics".

(**initiator , responder sessions********)
(*****************Real or random Secrecy*****************************************)
(********************************************************************************)
(******protocol Pi1 :The oracle reveals the actual Key if there is any*************)

(********************************************************************************)


Definition phi0  := [ msg (G 0) ; msg (g 0)].
Definition mphi0 := (conv_mylist_listm phi0).
Definition grn (n:nat) := (exp (G 0) (g 0) (r n)).

Definition x1 := (f mphi0).
(******start state****************)

Definition qa00:=  (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) (grn 1)  (if_then_else_M (EQ_M (to x1) (i 2)) (grn 2) O) ) .
 
(************************)
Definition t12:= msg qa00.
Definition phi1 := phi0 ++ [ t12 ].


(***********************************************************)

Definition mphi1 := (conv_mylist_listm phi1).
Definition mx1rn1 := (exp (G 0) (m x1) (r 1)).
Definition mx1rn2 := (exp (G 0) (m x1) (r 2)).
Definition grn2:= (exp (G 0) (g 0) (r 2)).

Definition x2 := (f mphi1).


(**********qa0000 -> qa1000, qa0010, qa0100, qa0001*************************************************)

Definition qa10 :=  (if_then_else_M (EQ_M (to x2) (i 1)) acc (if_then_else_M (EQ_M (to x2) (i 2)) (grn 2) O)).

Definition qa01:=   (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new) (grn 1) O).

Definition t13 := msg (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qa10  (if_then_else_M (EQ_M (to x1) (i 2)) qa01 O) ) .
Definition phi2:= phi1 ++ [t13].




(***************************************************************************)

Definition mphi2 := (conv_mylist_listm phi2).
Definition mx2rn1 := (exp (G 0) (m x2) (r 1)).
Definition mx2rn2 := (exp (G 0) (m x2) (r 2)).
Definition grn3:= (exp (G 0) (g 0) (r 3)).
Definition x3 := (f mphi2).



(************* qa1000 -> qbar, qa2000, qa1100, qa1001, qbar*******************************************************)

Definition qa20 :=   (if_then_else_M (EQ_M (to  x3) (i 2)) (grn 2) O).


Definition qa11 :=  (if_then_else_M (EQ_M (to  x3) (i 1)) acc O).

(*Definition qa02 :=  (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new) (grn 1) O).*)
Definition qa10_s :=  (if_then_else_M (EQ_M (to x2) (i 1)) qa20 (if_then_else_M (EQ_M (to x2) (i 2)) qa11 O)).




Definition qa01_s :=  (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new) qa11 O).




Definition t14 := msg (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qa10_s (if_then_else_M (EQ_M (to x1) (i 2)) qa01_s O) ) .

Definition phi3:= phi2 ++ [t14]. 
(***********************************************************************************************)
Definition mx3rn1 := (exp (G 0) (m x3) (r 1)).
Definition mx3rn2 := (exp (G 0) (m x3) (r 2)).
Definition mx3rn3 := (exp (G 0) (m x3) (r 3)).
Definition mphi3 := (conv_mylist_listm phi3).
Definition x4 := (f mphi3).
Definition grn4:= (exp (G 0) (g 0) (r  4)).

(********************qa2000 ->qbar, qa3000, qa2100, qa2001,qbar****************************************************)
(*Definition qa30 :=  (if_then_else_M (EQ_M (to  x4) (i 2)) (grn 2) O ).*)
  
Definition qa21 := (if_then_else_M ((EQ_M (reveal  x4) (i 2) ) & (EQ_M (to x1) (i 2))) mx1rn1    (if_then_else_M ((EQ_M (reveal  x4) (i 2) ) & (EQ_M (to x2) (i 2))) mx2rn2  (if_then_else_M ((EQ_M (reveal  x4) (i 2) ) & (EQ_M (to x3) (i 2))) mx3rn3
                                                                                                                                                                               (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to x2) (i 1)) &(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x2) new)) &(EQ_M (act x1) new)) mx2rn1
                                                                                                                                                                                               (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to x3) (i 1)) &(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new)) mx3rn1
                                           (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to x3) (i 1)) &(EQ_M (to x2) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x2) new)) mx3rn2 O)))))).


 

(*Definition qa12 := ( if_then_else_M (EQ_M (to x4) (i 1)) acc O).*)


(*****************************qa1001 -> qa1002, qa2001***************************************************)
Definition qa20_s :=  (if_then_else_M (EQ_M (to  x3) (i 2)) qa21 O).


Definition qa11_s :=  (if_then_else_M (EQ_M (to  x3) (i 1)) qa21 O).

(*Definition qa02_s :=  (if_then_else_M (EQ_M (to x3 ) (i 1)) & (EQ_M (act x3) new) qa12 O).*)
Definition qa10_ss :=  (if_then_else_M (EQ_M (to x2) (i 1)) qa20_s (if_then_else_M (EQ_M (to x2) (i 2)) qa11_s O)).

Definition qa01_ss:=   (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new) qa11_s O).

Definition t15 := msg  (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qa10_ss (if_then_else_M (EQ_M (to x1) (i 2)) qa01_ss O) ).

Definition phi4 :=  phi3 ++ [ t15 ]. 






(******************************************************************************************************************************************************)
(******************************************************************************************************************************************************)
(***********************protocol Pi2 : add transitions to qa2001************)
(***************************************************************************)



Definition phi21 := phi1.
Definition phi22 := phi2.
Definition phi23 := phi3.



Definition qb21 := (if_then_else_M (EQ_M (reveal  x4) (i 2) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 2))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) (grn 4) (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 2))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)))  (grn 4) (if_then_else_M ((EQ_M (reveal  x4) (i 2) ) & (EQ_M (to x1) (i 2))) mx1rn1    (if_then_else_M ((EQ_M (reveal  x4) (i 2) ) & (EQ_M (to x2) (i 2))) mx2rn2  (if_then_else_M ((EQ_M (reveal  x4) (i 2) ) & (EQ_M (to x3) (i 2))) mx3rn3
                                                                                                                                                                               (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to x2) (i 1)) &(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x2) new)) &(EQ_M (act x1) new)) mx2rn1
                                                                                                                                                                                               (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to x3) (i 1)) &(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new)) mx3rn1
                                           (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to x3) (i 1)) &(EQ_M (to x2) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x2) new)) mx3rn2 O)))))))).




(********************************************************************************)

Definition qb20_s :=  (if_then_else_M (EQ_M (to  x3) (i 2)) qb21 O) .


Definition qb11_s :=  (if_then_else_M (EQ_M (to  x3) (i 1)) qb21 O).


Definition qb10_ss := (if_then_else_M (EQ_M (to x2) (i 1)) qb20_s (if_then_else_M (EQ_M (to x2) (i 2)) qb11_s O)).

Definition qb01_ss:=   (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new) qb11_s O).

Definition t25 := msg  (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qb10_ss (if_then_else_M (EQ_M (to x1) (i 2)) qb01_ss O) ).













Definition phi24 :=  phi3 ++ [ t25 ]. 

(*********************************************************)


(************************************************************************************)
(************************************************************************************)
(************************Protocol Pi2'': replace the output grn4 by mx12rn2 , mx13rn1 in the term qb2001 in Pi2**********)
(************************************************************************************************************************)



Definition phi31 := phi1.
Definition phi32 := phi2.
Definition phi33 := phi3.


Definition qc21 := (if_then_else_M (EQ_M (reveal  x4) (i 2) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 2))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) mx2rn2 (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 2))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)))  mx3rn1   (if_then_else_M ((EQ_M (reveal  x4) (i 2) ) & (EQ_M (to x1) (i 2))) mx1rn1    (if_then_else_M ((EQ_M (reveal  x4) (i 2) ) & (EQ_M (to x2) (i 2))) mx2rn2  (if_then_else_M ((EQ_M (reveal  x4) (i 2) ) & (EQ_M (to x3) (i 2))) mx3rn3
                                                                                                                                                                               (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to x2) (i 1)) &(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x2) new)) &(EQ_M (act x1) new)) mx2rn1
                                                                                                                                                                                               (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to x3) (i 1)) &(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new)) mx3rn1
                                           (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to x3) (i 1)) &(EQ_M (to x2) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x2) new)) mx3rn2 O)))))))). 





(********************************************************************************)



Definition qc20_s :=  (if_then_else_M (EQ_M (to  x3) (i 2)) qc21 O) .


Definition qc11_s :=  (if_then_else_M (EQ_M (to  x3) (i 1)) qc21 O).


Definition qc10_ss :=  (if_then_else_M (EQ_M (to x2) (i 1)) qc20_s (if_then_else_M (EQ_M (to x2) (i 2)) qc11_s O)).

Definition qc01_ss:=  (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new) qc11_s O).

Definition t35 := msg  (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qc10_ss (if_then_else_M (EQ_M (to x1) (i 2)) qc01_ss O) ).













Definition phi34 :=  phi3 ++ [ t35 ]. 





(******************************Protocol Pi2' : replace the output grn4 by grn21 in the term qb2001 in Pi2********)
(****************************************************************************************************************)

Definition grn21:= (exp (G 0) (exp (G 0) (g 0) (r 2)) (r 1)).
Definition phi41 := phi1.
Definition phi42 := phi2.
Definition phi43 := phi3.



Definition qd21 := (if_then_else_M (EQ_M (reveal  x4) (i 2) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 2))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)) grn21 (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to  x3) (i 1)) &(EQ_M (to x2) (i 2))&(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new) &(EQ_M (m x2) (grn 1)) &(EQ_M (m  x3) (grn 2)))  grn21 (if_then_else_M ((EQ_M (reveal  x4) (i 2) ) & (EQ_M (to x1) (i 2))) mx1rn1    (if_then_else_M ((EQ_M (reveal  x4) (i 2) ) & (EQ_M (to x2) (i 2))) mx2rn2  (if_then_else_M ((EQ_M (reveal  x4) (i 2) ) & (EQ_M (to x3) (i 2))) mx3rn3
                                                                                                                                                                               (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to x2) (i 1)) &(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x2) new)) &(EQ_M (act x1) new)) mx2rn1
                                                                                                                                                                                               (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to x3) (i 1)) &(EQ_M (to x1) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x1) new)) mx3rn1
                                           (if_then_else_M ((EQ_M (reveal  x4) (i 1) ) & (EQ_M (to x3) (i 1)) &(EQ_M (to x2) (i 1)) & (notb (EQ_M ( act x3) new)) &(EQ_M (act x2) new)) mx3rn2 O))))))))   . 





(********************************************************************************)





Definition qd20_s :=   (if_then_else_M (EQ_M (to  x3) (i 2)) qd21 O) .


Definition qd11_s :=  (if_then_else_M (EQ_M (to  x3) (i 1)) qd21 O).


Definition qd10_ss :=  (if_then_else_M (EQ_M (to x2) (i 1)) qd20_s (if_then_else_M (EQ_M (to x2) (i 2)) qd11_s O)).

Definition qd01_ss:=   (if_then_else_M (EQ_M (to x2 ) (i 1)) & (EQ_M (act x2) new) qd11_s O).

Definition t45 := msg  (if_then_else_M ((EQ_M (to x1) (i 1)) & (EQ_M (act x1) new)) qd10_ss (if_then_else_M (EQ_M (to x1) (i 2)) qd01_ss O) ).



Definition phi44 :=  phi3 ++ [ t45 ]. 



