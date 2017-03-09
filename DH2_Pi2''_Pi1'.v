Load "DH2_Pi1_Pi2''".
  
 
Theorem pi2''_pi2': phi34 ~ phi44.

Proof. 

 repeat unf_phi. simpl. 
repeat unf. 


 
rewrite andB_assoc with (b2:= (EQ_M (m x2) (grn 1))).
rewrite andB_comm with (b1:= ((EQ_M (m x2) (grn 1)))).
rewrite <-andB_assoc with (b3:= (EQ_M (m x2) (grn 1))).
rewrite andB_comm with (b2:=  (EQ_M (m x2) (grn 1))).
unfold mx2rn2. 
 repeat rewrite EQ_BRmsg_msg' with (m1 := (m x2)) (m2:= (grn 1)) (m:= (m x2))   (m3:= (exp (G 0) (m x2) (r 2))) (b:=  (((((((EQ_M (reveal x4) (i 2)) & (EQ_M (to x3) (i 1))) &
                             (EQ_M (to x2) (i 2))) & 
                            (EQ_M (to x1) (i 1))) &
                           (notb (EQ_M (act x3) new))) & 
                          (EQ_M (act x1) new)) & (EQ_M (m x3) (grn 2)))).
 
simpl. 
rewrite andB_comm with (b1:=  (((((((EQ_M (reveal x4) (i 1)) &
                                 (EQ_M (to x3) (i 1))) & 
                                (EQ_M (to x2) (i 2))) & 
                               (EQ_M (to x1) (i 1))) &
                              (notb (EQ_M (act x3) new))) &
                             (EQ_M (act x1) new)) & 
                            (EQ_M (m x2) (grn 1)))) (b2:=  (EQ_M (m x3) (grn 2))) .
unfold mx3rn1.
simpl. 
repeat rewrite EQ_BRmsg_msg' with (m1 := (m x3)) (m2:= (grn 2)) (m:= (m x3))   (m3:= (exp (G 0) (m x3) (r 1)))  (b:=   (((((((EQ_M (reveal x4) (i 1)) &
                                 (EQ_M (to x3) (i 1))) & 
                                (EQ_M (to x2) (i 2))) & 
                               (EQ_M (to x1) (i 1))) &
                              (notb (EQ_M (act x3) new))) & 
                             (EQ_M (act x1) new)) & 
                            (EQ_M (m x2) (grn 1)))).
simpl.

rewrite commexp with (G:=  (pi1 (ggen (N 0)))) (g:=  (pi2 (ggen (N 0)))) (x:= (r 1)) (y:= (r 2)).
reflexivity. 
 
Qed.
