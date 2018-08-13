(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                   University of Missouri-Columbia.                   *)
(*                                                                      *)
(*                                                                      *)
(*                                                                      *)
(************************************************************************)
Load "DHprotocol".
(** * Real-or-random Secrecy *)

(** This library defines proofs of real-or-random secrecy of DH protocol. 

Basically, we prove two protocols two protocols [Pi1] and [Pi2] are indistinguishable, and are defined in the file [DHprot.v].
Since all the frames in the protocols are equal except the last one, it is enough to prove the last frames [phi4] in [Pi1] and [phi24] are indistinguishable, i.e., [phi4 ~ phi24]. *)

(** Tactics to unfold various terms. *)
Ltac unf_phi := try unfold phi0, phi1, phi2, phi3, phi4, phi24, phi34, phi44.
Ltac unf_trm:=  try unfold  t12, t13,t14, t15,t25 , t35, t45.
Ltac unf_qa := try unfold  qa00, qa10, qa01; try unfold qa10_s, qa01_s; try unfold qa10_ss, qa01_ss; try unfold qa20, qa11; try unfold qa20_s, qa11_s;  try unfold  qa21. 
Ltac unf_qb :=  try unfold qb21, qb20_s, qb11_s; try unfold qb10_ss, qb01_ss.
Ltac unf_qc :=   try unfold qc21, qc20_s, qc11_s; try unfold qc10_ss, qc01_ss.
Ltac unf_qd :=   try unfold qd21, qd20_s, qd11_s; try unfold qd10_ss, qd01_ss.
Ltac unf := try unf_phi; try unf_trm; try unf_qa ; try unf_qb ; try unf_qc; try unf_qd.

(** A tactic to apply [RESTR] for [n] times. *)

Ltac aply_proj n n2 H := 
match n with
| 0 => idtac
| S ?n' => restrproj_in n2 H; aply_proj n' n2 H
end.  


(**  Tactics *)

Ltac funappmconst t H := apply FUNCApp_mconst with (m:= t) in H; simpl in H.

Ltac funappbconst b1 H := apply FUNCApp_bconst with (b:= b1) in H; simpl in H.

Ltac funappf1 f n H:= apply FUNCApp_f1 with (f1:= f) (p:= n) in H; simpl in H.

Ltac funappf2mb f n1 n2 H:= apply FUNCApp_f2b with (f2b:= f) (p1:= n1) (p2:= n2) in H; simpl in H.

Ltac funappf2m f n1 n2 H:= apply FUNCApp_f2m with (f2m:= f) (p1:= n1) (p2:= n2) in H; simpl in H.

Ltac funappf3mb f n1 n2 n3 H:= apply FUNCApp_f3b with (f3b:= f) (p1:= n1) (p2:= n2) (p3:= n3) in H; simpl in H.

Ltac funappf3m f n1 n2 n3 H:= apply FUNCApp_f3m with (f3m:= f) (p1:= n1) (p2:= n2) (p3:= n3) in H; simpl in H.

Ltac funappifm  n1 n2 n3 H:= apply FUNCApp_f3bm with (f3bm:= ifm) (p1:= n1) (p2:= n2) (p3:= n3) in H; simpl in H.

Ltac funappifb  n1 n2 n3 H:= apply FUNCApp_g3 with (g3:= ifb) (p1:= n1) (p2:= n2) (p3:= n3) in H; simpl in H.

Ltac funappf2b f n1 n2 H:= apply FUNCApp_f1 with (g2:= f ) (p1 := n1 ) (p2:= n2) in H; simpl in H.

Ltac appconst H:=   funappmconst (i 1) H; funappmconst (i 2) H; funappmconst acc H; funappmconst O H;  funappmconst new H; funappbconst FAlse H; funappbconst TRue H;  try reflexivity.



Ltac checks x1 x2 H := funapptrmhyp (msg x1) (msg x2) H ;
                       funapptrmhyp (msg (to x1)) (msg (to x2)) H;
                       funapptrmhyp (msg (act x1)) (msg (act x2)) H;
                       funapptrmhyp (msg (reveal x1)) (msg (reveal x2)) H;
                       funapptrmhyp (bol (eqm (to x1) (i 1))) (bol (eqm (to x2) (i 1))) H;
                       funapptrmhyp (bol (eqm (to x1) (i 2))) (bol (eqm (to x2) (i 2))) H;
                       funapptrmhyp (bol (eqm (act x1) new)) (bol (eqm (act x2) new)) H;
                       funapptrmhyp (bol (eqm (to x1) (i 1) ) & (eqm (act x1) new)) (bol (eqm (to x1) (i 1) ) & (eqm (act x1) new))  H;
                       funapptrmhyp (bol (notb (eqm (act x1) new))) (bol (notb (eqm (act x2) new))) H;
                       funapptrmhyp (bol (eqm (reveal x1) (i 1))) (bol (eqm (reveal x2) (i 1))) H;
                       funapptrmhyp (bol (eqm (reveal x1) (i 2))) (bol (eqm (reveal x2) (i 2))) H;
                       funapptrmhyp (msg (m x1)) (msg (m x2)) H;
                       funapptrmhyp (bol (eqm (m x1) (grn 1))) (bol (eqm (m x2) (grn 1))) H;
                       funapptrmhyp (bol (eqm (m x1) (grn 2))) (bol (eqm (m x2) (grn 2))) H;
                       try reflexivity.


Ltac andBtac b1 b2 H:= funapptrmhyp (bol (b1&b2)) (bol (b1 & b2)) H; try reflexivity.

Ltac revtrm n x2 x3 x4 H := funapptrmhyp  (bol (eqm (reveal x4) (i n)) & (eqm (to x3) (i 1))) (bol (eqm (reveal x4) (i n)) & (eqm (to x3) (i 1))) H;
                            funapptrmhyp (bol (((eqm (reveal x4) (i n)) & (eqm (to x3) (i 1))) &
           (eqm (to x2) (i 2)))) (bol (((eqm (reveal x4) (i n)) & (eqm (to x3) (i 1))) &
           (eqm (to x2) (i 2)))) H;
                            funapptrmhyp (bol ((((eqm (reveal x4) (i n)) & (eqm (to x3) (i 1)))& (eqm (to x2) (i 2))) & (eqm (to x1) (i 1)))) (bol ((((eqm (reveal x4) (i n)) & (eqm (to x3) (i 1))) & (eqm (to x2) (i 2))) & (eqm (to x1) (i 1)))) H; 
                            funapptrmhyp (bol (((((eqm (reveal x4) (i n)) & (eqm (to x3) (i 1))) & (eqm (to x2) (i 2))) & (eqm (to x1) (i 1))) & (notb (eqm (act x3) new)))) (bol ((((eqm (reveal x4) (i n)) & (eqm (to x3) (i 1))) & (eqm (to x2) (i 2))) & (eqm (to x1) (i 1))) & (notb (eqm (act x3) new))) H;                                                                                                 funapptrmhyp (bol ((((((eqm (reveal x4) (i n)) & (eqm (to x3) (i 1))) &(eqm (to x2) (i 2))) & (eqm (to x1) (i 1))) & (notb (eqm (act x3) new))) & (eqm (act x1) new))) (bol ((((((eqm (reveal x4) (i n)) & (eqm (to x3) (i 1))) & (eqm (to x2) (i 2))) & (eqm (to x1) (i 1))) & (notb (eqm (act x3) new))) & (eqm (act x1) new)))  H;                                                   funapptrmhyp (bol (((((((eqm (reveal x4) (i n)) & (eqm (to x3) (i 1))) & (eqm (to x2) (i 2))) & (eqm (to x1) (i 1))) & (notb (eqm (act x3) new))) & (eqm (act x1) new)) & (eqm (m x2) (grn 1)))) (bol (((((((eqm (reveal x4) (i n)) & (eqm (to x3) (i 1))) & (eqm (to x2) (i 2))) & (eqm (to x1) (i 1))) &(notb (eqm (act x3) new))) & (eqm (act x1) new)) &(eqm (m x2) (grn 1)))) H; funapptrmhyp (bol (((((((eqm (reveal x4) (i n)) & (eqm (to x3) (i 1))) & (eqm (to x2) (i 2))) & (eqm (to x1) (i 1))) & (notb (eqm (act x3) new))) & (eqm (act x1) new)) & (eqm (m x2) (grn 1))) & (eqm (m x3) (grn 2)))  (bol (((((((eqm (reveal x4) (i n)) & (eqm (to x3) (i 1))) & (eqm (to x2) (i 2))) & (eqm (to x1) (i 1))) & (notb (eqm (act x3) new))) & (eqm (act x1) new)) & (eqm (m x2) (grn 1))) & (eqm (m x3) (grn 2))) H; try reflexivity.

(** To prove [phi4 ~ phi24], we first prove [phi4 ~ phi34], [phi34 ~ phi44], and [phi44 ~ phi24], where [phi34] and [phi44]
are frames of the protocols Pi2'' and Pi2' respectively. All these protocols are defined in the file [DHprot.v]. *)

Theorem Pi1_Pi2: phi4~phi24.
Proof.

(** Proof of [phi4 ~ phi34]. *)

assert( Pi1_Pi2'': phi4 ~ phi34).
repeat unf_phi. simpl.   
assert(H: (ostomsg t15) # (ostomsg t35)).  
simpl. 
repeat unf.
repeat rewrite andB_elm'' with (b1:= (eqm (to x1) (i 1)) )  (b2:= (eqm (act x1) new)).  
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
rewrite <- IFSAME_M with  (b:= (ifb (eqm (act (f mphi2tft)) new) FAlse TRue)).
aply_breq.
false_to_sesns_all; simpl. 
repeat redg;  repeat rewrite IFTFb.
aply_breq. 
repeat redg;  repeat rewrite IFTFb.
aply_breq.  
repeat redg;  repeat rewrite IFTFb. reflexivity. 
false_to_sesns_all; simpl. 
repeat redg;  repeat rewrite IFTFb. reflexivity.
apply eqm1 in H. rewrite H. reflexivity.
(** Proof of phi34 ~ phi44 .*)
assert(pi2''_pi2': phi34 ~ phi44).
repeat unf_phi. simpl.  
repeat unf.
assert( qc21 # qd21 ).  
repeat unf.
rewrite andB_assoc with (b2:= (eqm (m x2t) (grn 1))).
rewrite andB_comm with (b1:= ((eqm (m x2t) (grn 1)))).
rewrite <-andB_assoc with (b3:= (eqm (m x2t) (grn 1))).
rewrite andB_comm with (b2:=  (eqm (m x2t) (grn 1))).
unfold mx2trn2. 
repeat rewrite eqbrmsg_msg' with (m1 := (m x2t)) (m2:= (grn 1)) (m:= (m x2t))   (m3:= (exp (G 0) (m x2t) (r 2))) (b:=  (((((((eqm (reveal x4ttt) (i 2)) & (eqm (to x3tt) (i 1))) &
                             (eqm (to x2t) (i 2))) & 
                            (eqm (to x1) (i 1))) &
                           (notb (eqm (act x3tt) new))) & 
                          (eqm (act x1) new)) & (eqm (m x3tt) (grn 2)))). 
simpl.  
rewrite andB_comm with (b1:=  (((((((eqm (reveal x4ttt) (i 1)) &
                                 (eqm (to x3tt) (i 1))) & 
                                (eqm (to x2t) (i 2))) & 
                               (eqm (to x1) (i 1))) &
                              (notb (eqm (act x3tt) new))) &
                             (eqm (act x1) new)) & 
                            (eqm (m x2t) (grn 1)))) (b2:=  (eqm (m x3tt) (grn 2))) .
unfold mx3ttrn1.
simpl. 
repeat rewrite eqbrmsg_msg' with (m1 := (m x3tt)) (m2:= (grn 2)) (m:= (m x3tt))   (m3:= (exp (G 0) (m x3tt) (r 1)))  (b:=   (((((((eqm (reveal x4ttt) (i 1)) &
                                 (eqm (to x3tt) (i 1))) & 
                                (eqm (to x2t) (i 2))) & 
                               (eqm (to x1) (i 1))) &
                              (notb (eqm (act x3tt) new))) & 
                             (eqm (act x1) new)) & 
                            (eqm (m x2t) (grn 1)))).
simpl.
rewrite commexp with (G:=  (pi1 (ggen (N 0)))) (g:=  (pi2 (ggen (N 0)))) (x:= (r 1)) (y:= (r 2)).
reflexivity.
assert(qc21' # qd21' ).
unfold qc21', qd21'.
repeat unf. 
 rewrite andB_assoc with (b2:= (eqm (m x2t) (grn 1))).
rewrite andB_comm with (b1:= ((eqm (m x2t) (grn 1)))).
 rewrite <-andB_assoc with (b3:= (eqm (m x2t) (grn 1))).
 rewrite andB_comm with (b2:=  (eqm (m x2t) (grn 1))).
unfold mx2trn2. 
repeat rewrite eqbrmsg_msg' with (m1 := (m x2t)) (m2:= (grn 1)) (m:= (m x2t))   (m3:= (exp (G 0) (m x2t) (r 2))) (b:=  (((((((eqm (reveal x4tftt) (i 2)) & (eqm (to x3tft) (i 1))) &
                             (eqm (to x2t) (i 2))) & 
                            (eqm (to x1) (i 1))) &
                           (notb (eqm (act x3tft) new))) & 

                                                         (eqm (act x1) new)) & (eqm (m x3tft) (grn 2)))).
simpl.
rewrite andB_comm with (b1:=  ((((((eqm (reveal x4tftt) (i 1)) & (eqm (to x3tft) (i 1))) &
              (eqm (to x2t) (i 2))) & (eqm (to x1) (i 1))) &
            (notb (eqm (act x3tft) new))) & (eqm (act x1) new) & (eqm (m x2t) (grn 1)))) (b2:=  (eqm (m x3tft) (grn 2))) .
simpl.  
unfold mx3ttrn1. 
 rewrite eqbrmsg_msg' with (m1 := (m x3tft)) (m2:= (grn 2)) (m:= (m x3tft))   (m3:= (exp (G 0) (m x3tft) (r 1)))  (b:=     (((((((eqm (reveal x4tftt) (i 1)) & (eqm (to x3tft) (i 1))) &
              (eqm (to x2t) (i 2))) & (eqm (to x1) (i 1))) &
            (notb (eqm (act x3tft) new))) & (eqm (act x1) new)) &
          (eqm (m x2t) (grn 1)))).
simpl.
rewrite commexp with (G:=  (pi1 (ggen (N 0)))) (g:=  (pi2 (ggen (N 0)))) (x:= (r 1)) (y:= (r 2)).
reflexivity.
assert(qc21'' # qd21'').
unfold qc21'', qd21''.
rewrite andB_assoc with (b2:= (eqm (m x2ft) (grn 1))).
rewrite andB_comm with (b1:= ((eqm (m x2ft) (grn 1)))).
 rewrite <-andB_assoc with (b3:= (eqm (m x2ft) (grn 1))).
 rewrite andB_comm with (b2:=  (eqm (m x2ft) (grn 1))).
unfold mx2ftrn2. 
repeat rewrite eqbrmsg_msg' with (m1 := (m x2ft)) (m2:= (grn 1)) (m:= (m x2ft))   (m3:= (exp (G 0) (m x2ft) (r 2))) (b:=   (((((((eqm (reveal x4fttt) (i 2)) & (eqm (to x3ftt) (i 1))) &
           (eqm (to x2ft) (i 2))) & (eqm (to x1) (i 1))) &
         (notb (eqm (act x3ftt) new))) & (eqm (act x1) new)) &
       (eqm (m x3ftt) (grn 2)))). simpl. 
rewrite andB_comm with (b1:=  ((((((eqm (reveal x4fttt) (i 1)) & (eqm (to x3ftt) (i 1))) &
              (eqm (to x2ft) (i 2))) & (eqm (to x1) (i 1))) &
            (notb (eqm (act x3ftt) new))) & (eqm (act x1) new) & (eqm (m x2ft) (grn 1)))) (b2:=  (eqm (m x3ftt) (grn 2))) .
simpl.  
unfold mx3fttrn1.  

 rewrite eqbrmsg_msg' with (m1 := (m x3ftt)) (m2:= (grn 2)) (m:= (m x3ftt))   (m3:= (exp (G 0) (m x3ftt) (r 1)))  (b:=     (((((((eqm (reveal x4fttt) (i 1)) & (eqm (to x3ftt) (i 1))) &
              (eqm (to x2ft) (i 2))) & (eqm (to x1) (i 1))) &
            (notb (eqm (act x3ftt) new))) & (eqm (act x1) new)) &
          (eqm (m x2ft) (grn 1)))).
simpl.
rewrite commexp with (G:=  (pi1 (ggen (N 0)))) (g:=  (pi2 (ggen (N 0)))) (x:= (r 1)) (y:= (r 2)).
reflexivity.
unfold qc11'_s, qd11'_s.
rewrite H, H0, H1. reflexivity.
(** Proof of [phi44 ~ phi24] . *)

assert(Pi1'_Pi2: phi44 ~ phi24).
repeat unf_phi. simpl.
repeat unf. 
apply  IFBRANCH_M4 with (ml1:= [msg (G 0); msg (g 0)]) (ml2:= [msg (G 0); msg (g 0)]); try  reflexivity;  simpl. 
apply IFBRANCH_M3 with (ml1:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);  msg (grn 1)]) (ml2:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
                                                                                                                          msg (grn 1)]); try reflexivity; simpl.
apply IFBRANCH_M2 with (ml1:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new); msg (grn 1); bol (eqm (to x2t) (i 1)); msg acc]) (ml2:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new); msg (grn 1); bol (eqm (to x2t) (i 1)); msg acc]). simpl.
apply IFBRANCH_M1 with (ml1:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    msg (grn 1); bol (eqm (to x2t) (i 1)); msg acc;
    bol (eqm (to x3tt) (i 2)); msg (grn 2)]) (ml2:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
   msg (grn 1); bol (eqm (to x2t) (i 1)); msg acc; 
   bol (eqm (to x3tt) (i 2)); msg (grn 2)]); try reflexivity; simpl. 

DDH2.

appconst DDH1; checks x1 x1 DDH1; checks x2t x2t DDH1; checks x3tt x3tt DDH1; checks x4ttt x4ttt DDH1; revtrm 1 x2t x3tt x4ttt DDH1; revtrm 2 x2t x3tt x4ttt DDH1.
 unfold grn21.
  rewrite  <-commexp with (G:= (G 0)) (g:= (g 0))(x:= (r 1)) (y:= (r 2)).
 
      restrsublis DDH1.
      simpl.  
  (** subgoal-2*)
      DDH2.
     
apply IFBRANCH_M1 with (ml1:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    msg (grn 1); bol (eqm (to x2t) (i 1)); msg acc;
    bol (eqm (to x3tt) (i 2)); msg (grn 2);
    bol
      (((((((eqm (reveal x4ttt) (i 2)) & (eqm (to x3tt) (i 1))) &
           (eqm (to x2t) (i 2))) & (eqm (to x1) (i 1))) &
         (notb (eqm (act x3tt) new))) & (eqm (act x1) new)) &
       (eqm (m x2t) (grn 1))) & (eqm (m x3tt) (grn 2))]) (ml2:=[msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    msg (grn 1); bol (eqm (to x2t) (i 1)); msg acc;
    bol (eqm (to x3tt) (i 2)); msg (grn 2);
    bol
      (((((((eqm (reveal x4ttt) (i 2)) & (eqm (to x3tt) (i 1))) &
           (eqm (to x2t) (i 2))) & (eqm (to x1) (i 1))) &
         (notb (eqm (act x3tt) new))) & (eqm (act x1) new)) &
                                                            (eqm (m x2t) (grn 1))) & (eqm (m x3tt) (grn 2))]). simpl.
appconst DDH1;
checks x1 x1 DDH1; checks x2t x2t DDH1; checks x3tt x3tt DDH1; checks x4ttt x4ttt DDH1; revtrm 2 x2t x3tt x4ttt DDH1; revtrm 1 x2t x3tt x4ttt DDH1.
unfold grn21. 
rewrite <- commexp with (G:= (G 0)) (g:= (g 0)) (x:= (r 1)) (y:= (r 2)). 
restrsublis DDH1. 
(** subgoal-3 *)
simpl. 
apply IFBRANCH_M1 with (ml1:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    msg (grn 1); bol (eqm (to x2t) (i 1)); msg acc;
    bol (eqm (to x3tt) (i 2)); msg (grn 2);
    bol
      (((((((eqm (reveal x4ttt) (i 2)) & (eqm (to x3tt) (i 1))) &
           (eqm (to x2t) (i 2))) & (eqm (to x1) (i 1))) &
         (notb (eqm (act x3tt) new))) & (eqm (act x1) new)) &
       (eqm (m x2t) (grn 1))) & (eqm (m x3tt) (grn 2));
    bol
      (((((((eqm (reveal x4ttt) (i 1)) & (eqm (to x3tt) (i 1))) &
           (eqm (to x2t) (i 2))) & (eqm (to x1) (i 1))) &
         (notb (eqm (act x3tt) new))) & (eqm (act x1) new)) &
       (eqm (m x2t) (grn 1))) & (eqm (m x3tt) (grn 2))]) (ml2:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    msg (grn 1); bol (eqm (to x2t) (i 1)); msg acc;
    bol (eqm (to x3tt) (i 2)); msg (grn 2);
    bol
      (((((((eqm (reveal x4ttt) (i 2)) & (eqm (to x3tt) (i 1))) &
           (eqm (to x2t) (i 2))) & (eqm (to x1) (i 1))) &
         (notb (eqm (act x3tt) new))) & (eqm (act x1) new)) &
       (eqm (m x2t) (grn 1))) & (eqm (m x3tt) (grn 2));
    bol
      (((((((eqm (reveal x4ttt) (i 1)) & (eqm (to x3tt) (i 1))) &
           (eqm (to x2t) (i 2))) & (eqm (to x1) (i 1))) &
         (notb (eqm (act x3tt) new))) & (eqm (act x1) new)) &
       (eqm (m x2t) (grn 1))) & (eqm (m x3tt) (grn 2))]).
simpl;try reflexivity.    reflexivity. reflexivity.
(** subgoal-4 *)

apply IFBRANCH_M3 with (ml1:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
                               msg (grn 1); bol (eqm (to x2t) (i 1))]) (ml2:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new); msg (grn 1); bol (eqm (to x2t) (i 1))]).
simpl.
repeat unfold qd21', qb21'.
apply IFBRANCH_M2 with (ml1:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    msg (grn 1); bol (eqm (to x2t) (i 1)); bol (eqm (to x2t) (i 2));
    msg (grn 2)]) (ml2:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
   msg (grn 1); bol (eqm (to x2t) (i 1)); bol (eqm (to x2t) (i 2));
   msg (grn 2)]). simpl.
apply IFBRANCH_M1 with (ml1:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    msg (grn 1); bol (eqm (to x2t) (i 1)); bol (eqm (to x2t) (i 2));
    msg (grn 2); bol (eqm (to x3tft) (i 1)); msg acc]) (ml2:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    msg (grn 1); bol (eqm (to x2t) (i 1)); bol (eqm (to x2t) (i 2));
    msg (grn 2); bol (eqm (to x3tft) (i 1)); msg acc]). simpl.
DDH2. appconst DDH1;checks x1 x1 DDH1; checks x2t x2t DDH1; checks x3tft x3tft DDH1; checks x4tftt x4tftt DDH1; revtrm 1 x2t x3tft x4tftt DDH1; revtrm 2 x2t x3tft x4tftt DDH1.
unfold grn21.
rewrite <-commexp with (G:= (G 0)) (g:= (g 0)) (x:= (r 1)) (y:= (r 2)).
restrsublis DDH1.
(** subgoal-5 *)
simpl.
apply IFBRANCH_M1 with (ml1:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    msg (grn 1); bol (eqm (to x2t) (i 1)); bol (eqm (to x2t) (i 2));
    msg (grn 2); bol (eqm (to x3tft) (i 1)); msg acc;
    bol
      (((((((eqm (reveal x4tftt) (i 2)) & (eqm (to x3tft) (i 1))) &
           (eqm (to x2t) (i 2))) & (eqm (to x1) (i 1))) &
         (notb (eqm (act x3tft) new))) & (eqm (act x1) new)) &
       (eqm (m x2t) (grn 1))) & (eqm (m x3tft) (grn 2))]) (ml2:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    msg (grn 1); bol (eqm (to x2t) (i 1)); bol (eqm (to x2t) (i 2));
    msg (grn 2); bol (eqm (to x3tft) (i 1)); msg acc;
    bol
      (((((((eqm (reveal x4tftt) (i 2)) & (eqm (to x3tft) (i 1))) &
           (eqm (to x2t) (i 2))) & (eqm (to x1) (i 1))) &
         (notb (eqm (act x3tft) new))) & (eqm (act x1) new)) &
                                                             (eqm (m x2t) (grn 1))) & (eqm (m x3tft) (grn 2))]). simpl.

DDH2. 
appconst DDH1;checks x1 x1 DDH1; checks x2t x2t DDH1; checks x3tft x3tft DDH1; checks x4tftt x4tftt DDH1; revtrm 1 x2t x3tft x4tftt DDH1; revtrm 2 x2t x3tft x4tftt DDH1.
unfold grn21.
rewrite <- commexp with (G:=(G 0)) (g:= (g 0)) (x:= (r 1)) (y:= (r 2)).
restrsublis DDH1.
(** subgoal-6 *)
reflexivity. reflexivity. reflexivity.
(** subgoal-7 *)
simpl.
apply IFBRANCH_M4 with (ml1:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new)]) (ml2:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new)]).
simpl.
apply IFBRANCH_M3 with (ml1:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
                               bol (eqm (to x1) (i 2)); msg (grn 2)]) (ml2:=  [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new); bol (eqm (to x1) (i 2)); msg (grn 2)]). simpl.
unfold qa11', qd11'_s.
unfold qd21'', qb11'_s.
unfold qb21''.
apply IFBRANCH_M2 with (ml1:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    bol (eqm (to x1) (i 2)); msg (grn 2);
    bol (eqm (to x2ft) (i 1)) & (eqm (act x2ft) new); 
    msg (grn 1)]) (ml2:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    bol (eqm (to x1) (i 2)); msg (grn 2);
    bol (eqm (to x2ft) (i 1)) & (eqm (act x2ft) new); 
    msg (grn 1)]). simpl.
apply IFBRANCH_M1 with (ml1:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    bol (eqm (to x1) (i 2)); msg (grn 2);
    bol (eqm (to x2ft) (i 1)) & (eqm (act x2ft) new); 
    msg (grn 1); bol (eqm (to x3ftt) (i 1)); msg acc]) (ml2:=  [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
   bol (eqm (to x1) (i 2)); msg (grn 2);
   bol (eqm (to x2ft) (i 1)) & (eqm (act x2ft) new); 
   msg (grn 1); bol (eqm (to x3ftt) (i 1)); msg acc]).
simpl.
DDH2.   
appconst DDH1;checks x1 x1 DDH1; checks x2ft x2ft DDH1; checks x3ftt x3ftt DDH1; checks x4fttt x4fttt DDH1; revtrm 1 x2ft x3ftt x4fttt DDH1; revtrm 2 x2ft x3ftt x4fttt DDH1.
 unfold grn21. 
rewrite <- commexp with (G:=(G 0)) (g:= (g 0)) (x:= (r 1)) (y:= (r 2)).
restrsublis DDH1.
(** subgoal-8 *)
simpl.
apply IFBRANCH_M1 with (ml1:= [msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    bol (eqm (to x1) (i 2)); msg (grn 2);
    bol (eqm (to x2ft) (i 1)) & (eqm (act x2ft) new); 
    msg (grn 1); bol (eqm (to x3ftt) (i 1)); msg acc;
    bol
      (((((((eqm (reveal x4fttt) (i 2)) & (eqm (to x3ftt) (i 1))) &
           (eqm (to x2ft) (i 2))) & (eqm (to x1) (i 1))) &
         (notb (eqm (act x3ftt) new))) & (eqm (act x1) new)) &
       (eqm (m x2ft) (grn 1))) & (eqm (m x3ftt) (grn 2))]) (ml2:=[msg (G 0); msg (g 0); bol (eqm (to x1) (i 1)) & (eqm (act x1) new);
    bol (eqm (to x1) (i 2)); msg (grn 2);
    bol (eqm (to x2ft) (i 1)) & (eqm (act x2ft) new); 
    msg (grn 1); bol (eqm (to x3ftt) (i 1)); msg acc;
    bol
      (((((((eqm (reveal x4fttt) (i 2)) & (eqm (to x3ftt) (i 1))) &
           (eqm (to x2ft) (i 2))) & (eqm (to x1) (i 1))) &
         (notb (eqm (act x3ftt) new))) & (eqm (act x1) new)) &
                                                             (eqm (m x2ft) (grn 1))) & (eqm (m x3ftt) (grn 2))]). simpl.
DDH2.
 
appconst DDH1;checks x1 x1 DDH1; checks x2ft x2ft DDH1; checks x3ftt x3ftt DDH1; checks x4fttt x4fttt DDH1; revtrm 1 x2ft x3ftt x4fttt DDH1; revtrm 2 x2ft x3ftt x4fttt DDH1.
 unfold grn21. 
rewrite <- commexp with (G:=(G 0)) (g:= (g 0)) (x:= (r 1)) (y:= (r 2)).
restrsublis DDH1.
(** subgoal-9 *)
simpl. reflexivity. reflexivity. reflexivity.  reflexivity.
 apply EQI_trans with (ml2:= phi34);try assumption.
apply EQI_trans with (ml2:= phi44); try assumption.
Qed.