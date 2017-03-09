Load "tact_DH2".

  
  
 

Theorem Pi1_Pi2'': phi4 ~ phi34.
Proof.


  repeat unf_phi. 
simpl. 
  
assert(H: (ostomsg t15) # (ostomsg t35)).
simpl.
 
 repeat unf.

repeat rewrite andB_elm'' with (b1:= (EQ_M (to x1) (i 1)) ) (b2:= (EQ_M (act x1) new)  ).
 false_to_sesns_all; simpl. 
repeat redg; repeat rewrite IFTFb.
aply_breq.
 repeat redg;  repeat rewrite IFTFb. 
aply_breq.  
 repeat redg;  repeat rewrite IFTFb.
false_to_sesns_all; simpl. 
 repeat redg;  repeat rewrite IFTFb.
aply_breq.  
 repeat redg;  repeat rewrite IFTFb.
false_to_sesns_all; simpl. 
  repeat redg;  repeat rewrite IFTFb.
aply_breq.  
 repeat redg;  repeat rewrite IFTFb.
false_to_sesns_all; simpl. 
  repeat redg;  repeat rewrite IFTFb.
 aply_breq.  
 repeat redg;  repeat rewrite IFTFb.
repeat aply_andB_elm.
false_to_sesns_all; simpl. 
repeat redg;  repeat rewrite IFTFb.
 aply_breq.  
 repeat redg;  repeat rewrite IFTFb. reflexivity. 
false_to_sesns_all; simpl. 
repeat redg;  repeat rewrite IFTFb.
 aply_breq.  
 repeat redg;  repeat rewrite IFTFb.
aply_breq.  
 repeat redg;  repeat rewrite IFTFb. reflexivity. 
false_to_sesns_all; simpl. 
 repeat redg;  repeat rewrite IFTFb.
aply_breq.  
apply eqm in H. rewrite H. reflexivity. 

Qed.
 