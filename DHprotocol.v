(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                   University of Missouri-Columbia.                   *)
(*                                                                      *)
(*                                                                      *)
(*                                                                      *)
(************************************************************************)
Load "auxthms".
(** # This library defines DH protocol for two sessions, initiator and responder. 

Real-or-random secrecy is defined as two protocols, one in which the actual shared key is revealed and the one in which randomly generated key is revealed at the end of the protocol, are indistinguishable. #*)

(** [Pi1] is a protocol in which actual key is revealed at the end. 

Frame [phi0] represents initial knowledge of the attacker. *)
Definition phi0  := [ msg (G 0) ; msg (g 0)].

(** Frame [phi1] is constructed in the following way. *)

Definition mphi0 := (conv_mylist_listm phi0).
Definition grn (n:nat) := (exp (G 0) (g 0) (r n)).
Definition x1 := (f mphi0).
Definition qa00:=  (ifm ((eqm (to x1) (i 1)) & (eqm (act x1) new)) (grn 1)  (ifm (eqm (to x1) (i 2)) (grn 2) O) ) .
Definition t12:= msg qa00.
Definition phi1 := phi0 ++ [ t12 ].

(** Similarly frame [phi2] is computed. *)

Definition mphi1 := (conv_mylist_listm phi1).
Definition mx1rn1 := (exp (G 0) (m x1) (r 1)).
Definition mx1rn2 := (exp (G 0) (m x1) (r 2)). 
Definition x2 := (f mphi1).
Definition mphi1t:= (conv_mylist_listm (phi0 ++ [msg (grn 1)])).
Definition x2t := (f mphi1t).
Definition mphi1ft := (conv_mylist_listm (phi0 ++ [msg (grn 2)])).
Definition x2ft :=  (f mphi1ft).
(*qa00 -> qa10, qa01*)

Definition qa10 :=  (ifm (eqm (to x2t) (i 1)) acc (ifm (eqm (to x2t) (i 2)) (grn 2) O)).
Definition qa01:=   (ifm (eqm (to x2ft ) (i 1)) & (eqm (act x2ft) new) (grn 1) O).
Definition t13 := msg (ifm ((eqm (to x1) (i 1)) & (eqm (act x1) new)) qa10  (ifm (eqm (to x1) (i 2)) qa01 O) ) .
Definition phi2:= phi1 ++ [t13].

(** Frame [phi3] computed here. *)

Definition mphi2 := (conv_mylist_listm phi2).
Definition mx2trn1 := (exp (G 0) (m x2t) (r 1)).
Definition mx2trn2 := (exp (G 0) (m x2t) (r 2)).
Definition mx2ftrn1 := (exp (G 0) (m x2ft) (r 1)).
Definition mx2ftrn2 := (exp (G 0) (m x2ft) (r 2)).
Definition x3 := (f mphi2). 
Definition mphi2tt := (app mphi1t  [acc]).
Definition x3tt := (f mphi2tt).
Definition mphi2tft := (app mphi1t  [grn 2]).
Definition x3tft := (f mphi2tft).
Definition mphi2ftt := (app mphi1ft [grn 1]).
Definition x3ftt := (f mphi2ftt).

(*qa10-> qa20, qa11*)

Definition qa20 :=   (ifm (eqm (to  x3tt) (i 2)) (grn 2) O).
Definition qa11 :=  (ifm (eqm (to  x3tft) (i 1)) acc O).
Definition qa11' := (ifm (eqm (to x3ftt) (i 1)) acc O).
Definition qa10_s :=  (ifm (eqm (to x2t) (i 1)) qa20 (ifm (eqm (to x2t) (i 2)) qa11 O)).
Definition qa01_s :=  (ifm (eqm (to x2ft ) (i 1)) & (eqm (act x2ft) new) qa11' O).
Definition t14 := msg (ifm ((eqm (to x1) (i 1)) & (eqm (act x1) new)) qa10_s (ifm (eqm (to x1) (i 2)) qa01_s O) ) .
Definition phi3:= phi2 ++ [t14].


(** The frame [phi4] representes knowledge of the attacker at the end of the protocol. *)
 Definition mx3ttrn1 := (exp (G 0) (m x3tt) (r 1)).
Definition mx3ttrn2 := (exp (G 0) (m x3tt) (r 2)).
Definition mx3ttrn3 := (exp (G 0) (m x3tt) (r 3)).
 Definition mx3tftrn1 := (exp (G 0) (m x3tft) (r 1)).
Definition mx3tftrn2 := (exp (G 0) (m x3tft) (r 2)).
Definition mx3tftrn3 := (exp (G 0) (m x3tft) (r 3)).
 Definition mx3fttrn1 := (exp (G 0) (m x3ftt) (r 1)).
Definition mx3fttrn2 := (exp (G 0) (m x3ftt) (r 2)).
Definition mx3fttrn3 := (exp (G 0) (m x3ftt) (r 3)). 
Definition mphi3 := (conv_mylist_listm phi3).
Definition mphi3ttt := (app mphi2tt [grn 2]).
Definition x4ttt := (f mphi3ttt).
Definition mphi3tftt := (app mphi2tft [acc]).
Definition x4tftt := (f mphi3tftt).
Definition mphi3fttt := (app mphi2ftt [acc]).
Definition x4fttt := (f mphi3fttt).

     
Definition qa21 := (ifm ((eqm (reveal  x4ttt) (i 2) ) & (eqm (to x1) (i 2))) mx1rn1    (ifm ((eqm (reveal  x4ttt) (i 2) ) & (eqm (to x2t) (i 2))) mx2trn2  (ifm ((eqm (reveal  x4ttt) (i 2) ) & (eqm (to x3tt) (i 2))) mx3ttrn3
                                                                                                                                                                               (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to x2t) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x2t) new)) &(eqm (act x1) new)) mx2trn1
                                                                                                                                                                                               (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to x3tt) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x3tt) new)) &(eqm (act x1) new)) mx3ttrn1
                                                                                                                                                                                                    (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to x3tt) (i 1)) &(eqm (to x2t) (i 1)) & (notb (eqm ( act x3tt) new)) &(eqm (act x2t) new)) mx3ttrn2 O)))))).


Definition qa21' := (ifm ((eqm (reveal  x4tftt) (i 2) ) & (eqm (to x1) (i 2))) mx1rn1    (ifm ((eqm (reveal  x4tftt) (i 2) ) & (eqm (to x2t) (i 2))) mx2trn2  (ifm ((eqm (reveal  x4tftt) (i 2) ) & (eqm (to x3tft) (i 2))) mx3tftrn3
                                                                                                                                                                               (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to x2t) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x2t) new)) &(eqm (act x1) new)) mx2trn1
                                                                                                                                                                                               (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to x3tft) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x3tft) new)) &(eqm (act x1) new)) mx3tftrn1
                                                                                                                                                                                                    (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to x3tft) (i 1)) &(eqm (to x2t) (i 1)) & (notb (eqm ( act x3tft) new)) &(eqm (act x2t) new)) mx3tftrn2 O)))))).

Definition qa21'' := (ifm ((eqm (reveal  x4fttt) (i 2) ) & (eqm (to x1) (i 2))) mx1rn1    (ifm ((eqm (reveal  x4fttt) (i 2) ) & (eqm (to x2ft) (i 2))) mx2ftrn2  (ifm ((eqm (reveal  x4fttt) (i 2) ) & (eqm (to x3ftt) (i 2))) mx3fttrn3
                                                                                                                                                                               (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to x2ft) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x2ft) new)) &(eqm (act x1) new)) mx2ftrn1
                                                                                                                                                                                               (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to x3ftt) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x3ftt) new)) &(eqm (act x1) new)) mx3fttrn1
                                           (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to x3ftt) (i 1)) &(eqm (to x2ft) (i 1)) & (notb (eqm ( act x3ftt) new)) &(eqm (act x2ft) new)) mx3fttrn2 O)))))).

Definition qa20_s :=  (ifm (eqm (to  x3tt) (i 2)) qa21 O).
Definition qa11_s :=  (ifm (eqm (to  x3tft) (i 1)) qa21' O).
Definition qa11'_s := (ifm (eqm (to x3ftt) (i 1)) qa21'' O).

Definition qa10_ss :=  (ifm (eqm (to x2t) (i 1)) qa20_s (ifm (eqm (to x2t) (i 2)) qa11_s O)).
Definition qa01_ss:=   (ifm (eqm (to x2ft ) (i 1)) & (eqm (act x2ft) new) qa11'_s O).
Definition t15 := msg  (ifm ((eqm (to x1) (i 1)) & (eqm (act x1) new)) qa10_ss (ifm (eqm (to x1) (i 2)) qa01_ss O) ).
Definition phi4 :=  phi3 ++ [ t15 ].

(** Now we define a protocol [Pi2] that reveals a randomly generated key at the end.

Note that all the frames in [Pi2], initial and intermediate, are same equivalent to the frames in [Pi1] except the last frame [phi4], and we define the last frame and call it as [phi24]. The frame [phi24] outputs a randomly generated key in lieu of actual key in [phi4]. *)

 
Definition qb21 := (ifm (eqm (reveal  x4ttt) (i 2) ) & (eqm (to  x3tt) (i 1)) &(eqm (to x2t) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3tt) new)) &(eqm (act x1) new) &(eqm (m x2t) (grn 1)) &(eqm (m  x3tt) (grn 2)) (grn 4) (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to  x3tt) (i 1)) &(eqm (to x2t) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3tt) new)) &(eqm (act x1) new) &(eqm (m x2t) (grn 1)) &(eqm (m  x3tt) (grn 2)))  (grn 4) (ifm ((eqm (reveal  x4ttt) (i 2) ) & (eqm (to x1) (i 2))) mx1rn1    (ifm ((eqm (reveal  x4ttt) (i 2) ) & (eqm (to x2t) (i 2))) mx2trn2  (ifm ((eqm (reveal  x4ttt) (i 2) ) & (eqm (to x3tt) (i 2))) mx3ttrn3
                                                                                                                                                                               (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to x2t) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x2t) new)) &(eqm (act x1) new)) mx2trn1
                                                                                                                                                                                               (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to x3tt) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x3tt) new)) &(eqm (act x1) new)) mx3ttrn1
                                                                                                                                                                                                    (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to x3tt) (i 1)) &(eqm (to x2t) (i 1)) & (notb (eqm ( act x3tt) new)) &(eqm (act x2t) new)) mx3ttrn2 O)))))))).

                                                                                                                                                                                                Definition qb21' :=      (ifm (eqm (reveal  x4tftt) (i 2) ) & (eqm (to  x3tft) (i 1)) &(eqm (to x2t) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3tft) new)) &(eqm (act x1) new) &(eqm (m x2t) (grn 1)) &(eqm (m  x3tft) (grn 2)) (grn 4) (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to  x3tft) (i 1)) &(eqm (to x2t) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3tft) new)) &(eqm (act x1) new) &(eqm (m x2t) (grn 1)) &(eqm (m  x3tft) (grn 2)))  (grn 4)   (ifm ((eqm (reveal  x4tftt) (i 2) ) & (eqm (to x1) (i 2))) mx1rn1    (ifm ((eqm (reveal  x4tftt) (i 2) ) & (eqm (to x2t) (i 2))) mx2trn2  (ifm ((eqm (reveal  x4tftt) (i 2) ) & (eqm (to x3tft) (i 2))) mx3tftrn3
                                                                                                                                                                               (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to x2t) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x2t) new)) &(eqm (act x1) new)) mx2trn1
                                                                                                                                                                                               (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to x3tft) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x3tft) new)) &(eqm (act x1) new)) mx3tftrn1
                                                                                                                                                                                                    (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to x3tft) (i 1)) &(eqm (to x2t) (i 1)) & (notb (eqm ( act x3tft) new)) &(eqm (act x2t) new)) mx3tftrn2 O)))))))).
                                                                                                                                                                                                                                                                                                                                                                                                                               Definition qb21'' :=  (ifm (eqm (reveal  x4fttt) (i 2) ) & (eqm (to  x3ftt) (i 1)) &(eqm (to x2ft) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3ftt) new)) &(eqm (act x1) new) &(eqm (m x2ft) (grn 1)) &(eqm (m  x3ftt) (grn 2)) (grn 4) (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to  x3ftt) (i 1)) &(eqm (to x2ft) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3ftt) new)) &(eqm (act x1) new) &(eqm (m x2ft) (grn 1)) &(eqm (m  x3ftt) (grn 2)))  (grn 4) (ifm ((eqm (reveal  x4fttt) (i 2) ) & (eqm (to x1) (i 2))) mx1rn1    (ifm ((eqm (reveal  x4fttt) (i 2) ) & (eqm (to x2ft) (i 2))) mx2ftrn2  (ifm ((eqm (reveal  x4fttt) (i 2) ) & (eqm (to x3ftt) (i 2))) mx3fttrn3
                                                                                                                                                                               (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to x2ft) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x2ft) new)) &(eqm (act x1) new)) mx2ftrn1
                                                                                                                                                                                               (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to x3ftt) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x3ftt) new)) &(eqm (act x1) new)) mx3fttrn1
                                                                                                                                                                                                    (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to x3ftt) (i 1)) &(eqm (to x2ft) (i 1)) & (notb (eqm ( act x3ftt) new)) &(eqm (act x2ft) new)) mx3fttrn2 O)))))))).
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           Definition qb20_s :=  (ifm (eqm (to  x3tt) (i 2)) qb21 O).
Definition qb11_s :=  (ifm (eqm (to  x3tft) (i 1)) qb21' O).
Definition qb11'_s := (ifm (eqm (to x3ftt) (i 1)) qb21'' O).

Definition qb10_ss :=  (ifm (eqm (to x2t) (i 1)) qb20_s (ifm (eqm (to x2t) (i 2)) qb11_s O)).
Definition qb01_ss:=   (ifm (eqm (to x2ft ) (i 1)) & (eqm (act x2ft) new) qb11'_s O).
Definition t25 := msg  (ifm ((eqm (to x1) (i 1)) & (eqm (act x1) new)) qb10_ss (ifm (eqm (to x1) (i 2)) qb01_ss O) ).
Definition phi24 :=  phi3 ++ [ t25 ].

(** We define a protocol [Pi2''], that replaces the output actual shared key of the one branch by [mx2rn2] and other by [mx3rn1] in the protocol [Pi2]. *)
 
Definition qc21 := (ifm (eqm (reveal  x4ttt) (i 2) ) & (eqm (to  x3tt) (i 1)) &(eqm (to x2t) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3tt) new)) &(eqm (act x1) new) &(eqm (m x2t) (grn 1)) &(eqm (m  x3tt) (grn 2)) mx2trn2 (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to  x3tt) (i 1)) &(eqm (to x2t) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3tt) new)) &(eqm (act x1) new) &(eqm (m x2t) (grn 1)) &(eqm (m  x3tt) (grn 2)))  mx3ttrn1 (ifm ((eqm (reveal  x4ttt) (i 2) ) & (eqm (to x1) (i 2))) mx1rn1    (ifm ((eqm (reveal  x4ttt) (i 2) ) & (eqm (to x2t) (i 2))) mx2trn2  (ifm ((eqm (reveal  x4ttt) (i 2) ) & (eqm (to x3tt) (i 2))) mx3ttrn3
                                                                                                                                                                               (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to x2t) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x2t) new)) &(eqm (act x1) new)) mx2trn1
                                                                                                                                                                                               (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to x3tt) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x3tt) new)) &(eqm (act x1) new)) mx3ttrn1
                                                                                                                                                                                                    (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to x3tt) (i 1)) &(eqm (to x2t) (i 1)) & (notb (eqm ( act x3tt) new)) &(eqm (act x2t) new)) mx3ttrn2 O)))))))).

                                                                                                                                                                                                Definition qc21' :=      (ifm (eqm (reveal  x4tftt) (i 2) ) & (eqm (to  x3tft) (i 1)) &(eqm (to x2t) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3tft) new)) &(eqm (act x1) new) &(eqm (m x2t) (grn 1)) &(eqm (m  x3tft) (grn 2)) mx2trn2 (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to  x3tft) (i 1)) &(eqm (to x2t) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3tft) new)) &(eqm (act x1) new) &(eqm (m x2t) (grn 1)) &(eqm (m  x3tft) (grn 2)))  mx3tftrn1   (ifm ((eqm (reveal  x4tftt) (i 2) ) & (eqm (to x1) (i 2))) mx1rn1    (ifm ((eqm (reveal  x4tftt) (i 2) ) & (eqm (to x2t) (i 2))) mx2trn2  (ifm ((eqm (reveal  x4tftt) (i 2) ) & (eqm (to x3tft) (i 2))) mx3tftrn3
                                                                                                                                                                               (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to x2t) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x2t) new)) &(eqm (act x1) new)) mx2trn1
                                                                                                                                                                                               (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to x3tft) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x3tft) new)) &(eqm (act x1) new)) mx3tftrn1
                                                                                                                                                                                                    (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to x3tft) (i 1)) &(eqm (to x2t) (i 1)) & (notb (eqm ( act x3tft) new)) &(eqm (act x2t) new)) mx3tftrn2 O)))))))).
                                                                                                                                                                                                                                                                                                                                                                                                                               Definition qc21'' :=  (ifm (eqm (reveal  x4fttt) (i 2) ) & (eqm (to  x3ftt) (i 1)) &(eqm (to x2ft) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3ftt) new)) &(eqm (act x1) new) &(eqm (m x2ft) (grn 1)) &(eqm (m  x3ftt) (grn 2)) mx2ftrn2 (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to  x3ftt) (i 1)) &(eqm (to x2ft) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3ftt) new)) &(eqm (act x1) new) &(eqm (m x2ft) (grn 1)) &(eqm (m  x3ftt) (grn 2)))  mx3fttrn1 (ifm ((eqm (reveal  x4fttt) (i 2) ) & (eqm (to x1) (i 2))) mx1rn1    (ifm ((eqm (reveal  x4fttt) (i 2) ) & (eqm (to x2ft) (i 2))) mx2ftrn2  (ifm ((eqm (reveal  x4fttt) (i 2) ) & (eqm (to x3ftt) (i 2))) mx3fttrn3
                                                                                                                                                                               (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to x2ft) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x2ft) new)) &(eqm (act x1) new)) mx2ftrn1
                                                                                                                                                                                               (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to x3ftt) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x3ftt) new)) &(eqm (act x1) new)) mx3fttrn1
                                                                                                                                                                                                    (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to x3ftt) (i 1)) &(eqm (to x2ft) (i 1)) & (notb (eqm ( act x3ftt) new)) &(eqm (act x2ft) new)) mx3fttrn2 O)))))))).
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           Definition qc20_s :=  (ifm (eqm (to  x3tt) (i 2)) qc21 O).
Definition qc11_s :=  (ifm (eqm (to  x3tft) (i 1)) qc21' O).
Definition qc11'_s := (ifm (eqm (to x3ftt) (i 1)) qc21'' O).

Definition qc10_ss :=  (ifm (eqm (to x2t) (i 1)) qc20_s (ifm (eqm (to x2t) (i 2)) qc11_s O)).
Definition qc01_ss:=   (ifm (eqm (to x2ft ) (i 1)) & (eqm (act x2ft) new) qc11'_s O).
Definition t35 := msg  (ifm ((eqm (to x1) (i 1)) & (eqm (act x1) new)) qc10_ss (ifm (eqm (to x1) (i 2)) qc01_ss O) ).
Definition phi34 :=  phi3 ++ [ t35 ].

(** We also define a protocol [Pi2'] that replaces the randomly generated output by [g^(ab) (grn 21)] in the protocol [Pi2]. *)
Definition grn21 := (exp (G 0) (grn 2) (r 1)). 

Definition qd21 := (ifm (eqm (reveal  x4ttt) (i 2) ) & (eqm (to  x3tt) (i 1)) &(eqm (to x2t) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3tt) new)) &(eqm (act x1) new) &(eqm (m x2t) (grn 1)) &(eqm (m  x3tt) (grn 2)) grn21 (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to  x3tt) (i 1)) &(eqm (to x2t) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3tt) new)) &(eqm (act x1) new) &(eqm (m x2t) (grn 1)) &(eqm (m  x3tt) (grn 2))) grn21 (ifm ((eqm (reveal  x4ttt) (i 2) ) & (eqm (to x1) (i 2))) mx1rn1    (ifm ((eqm (reveal  x4ttt) (i 2) ) & (eqm (to x2t) (i 2))) mx2trn2  (ifm ((eqm (reveal  x4ttt) (i 2) ) & (eqm (to x3tt) (i 2))) mx3ttrn3
                                                                                                                                                                               (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to x2t) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x2t) new)) &(eqm (act x1) new)) mx2trn1
                                                                                                                                                                                               (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to x3tt) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x3tt) new)) &(eqm (act x1) new)) mx3ttrn1
                                                                                                                                                                                                    (ifm ((eqm (reveal  x4ttt) (i 1) ) & (eqm (to x3tt) (i 1)) &(eqm (to x2t) (i 1)) & (notb (eqm ( act x3tt) new)) &(eqm (act x2t) new)) mx3ttrn2 O)))))))).

                                                                                                                                                                                                Definition qd21' :=      (ifm (eqm (reveal  x4tftt) (i 2) ) & (eqm (to  x3tft) (i 1)) &(eqm (to x2t) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3tft) new)) &(eqm (act x1) new) &(eqm (m x2t) (grn 1)) &(eqm (m  x3tft) (grn 2)) grn21 (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to  x3tft) (i 1)) &(eqm (to x2t) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3tft) new)) &(eqm (act x1) new) &(eqm (m x2t) (grn 1)) &(eqm (m  x3tft) (grn 2))) grn21  (ifm ((eqm (reveal  x4tftt) (i 2) ) & (eqm (to x1) (i 2))) mx1rn1    (ifm ((eqm (reveal  x4tftt) (i 2) ) & (eqm (to x2t) (i 2))) mx2trn2  (ifm ((eqm (reveal  x4tftt) (i 2) ) & (eqm (to x3tft) (i 2))) mx3tftrn3
                                                                                                                                                                               (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to x2t) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x2t) new)) &(eqm (act x1) new)) mx2trn1
                                                                                                                                                                                               (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to x3tft) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x3tft) new)) &(eqm (act x1) new)) mx3tftrn1
                                                                                                                                                                                                    (ifm ((eqm (reveal  x4tftt) (i 1) ) & (eqm (to x3tft) (i 1)) &(eqm (to x2t) (i 1)) & (notb (eqm ( act x3tft) new)) &(eqm (act x2t) new)) mx3tftrn2 O)))))))).
                                                                                                                                                                                                                                                                                                                                                                                         Definition qd21'' :=  (ifm (eqm (reveal  x4fttt) (i 2) ) & (eqm (to  x3ftt) (i 1)) &(eqm (to x2ft) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3ftt) new)) &(eqm (act x1) new) &(eqm (m x2ft) (grn 1)) &(eqm (m  x3ftt) (grn 2)) grn21 (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to  x3ftt) (i 1)) &(eqm (to x2ft) (i 2))&(eqm (to x1) (i 1)) & (notb (eqm ( act x3ftt) new)) &(eqm (act x1) new) &(eqm (m x2ft) (grn 1)) &(eqm (m  x3ftt) (grn 2)))  grn21 (ifm ((eqm (reveal  x4fttt) (i 2) ) & (eqm (to x1) (i 2))) mx1rn1    (ifm ((eqm (reveal  x4fttt) (i 2) ) & (eqm (to x2ft) (i 2))) mx2ftrn2  (ifm ((eqm (reveal  x4fttt) (i 2) ) & (eqm (to x3ftt) (i 2))) mx3fttrn3
                                                                                                                                                                               (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to x2ft) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x2ft) new)) &(eqm (act x1) new)) mx2ftrn1
                                                                                                                                                                                               (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to x3ftt) (i 1)) &(eqm (to x1) (i 1)) & (notb (eqm ( act x3ftt) new)) &(eqm (act x1) new)) mx3fttrn1
                                                                                                                                                                                                    (ifm ((eqm (reveal  x4fttt) (i 1) ) & (eqm (to x3ftt) (i 1)) &(eqm (to x2ft) (i 1)) & (notb (eqm ( act x3ftt) new)) &(eqm (act x2ft) new)) mx3fttrn2 O)))))))).
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Definition qd20_s :=  (ifm (eqm (to  x3tt) (i 2)) qd21 O).
Definition qd11_s :=  (ifm (eqm (to  x3tft) (i 1)) qd21' O).
Definition qd11'_s := (ifm (eqm (to x3ftt) (i 1)) qd21'' O).

Definition qd10_ss :=  (ifm (eqm (to x2t) (i 1)) qd20_s (ifm (eqm (to x2t) (i 2)) qd11_s O)).
Definition qd01_ss:=   (ifm (eqm (to x2ft ) (i 1)) & (eqm (act x2ft) new) qd11'_s O).
Definition t45 := msg  (ifm ((eqm (to x1) (i 1)) & (eqm (act x1) new)) qd10_ss (ifm (eqm (to x1) (i 2)) qd01_ss O) ).
Definition phi44 :=  phi3 ++ [ t45 ].

(** Real-or-random secrecy in this case is that proving two protocols [Pi1] and [Pi2] are computationally distinguishable, i.e., [Pi1~Pi2]. *)




