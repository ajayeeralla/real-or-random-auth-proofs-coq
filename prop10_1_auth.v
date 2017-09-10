(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                     Rohit Chadha <chadhar@missouri.edu>              *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)
Load "dsaxioms".
Section dh_auth.
(** This library contains proof of the responder's authentication of the initior of authenticated version of the DH protocol (STS protocol). *)

(** # <b> Authenticated version of the DH protocol:</b>
</br>
Group description G and g are generated honestly, according to a randomized algorithm and are made public.
Public key, secret key pairs (pkA , skA ) and (pkB , skB ) are generated honestly for both A and B and pkA , pkB are made public.
<ul>
<li> The Initiator generates a random <i> a </i> in <i> Z<sub>|g|</sub> </i> and sends <i> g<sup>a</sup>. </li> 
<li> The Responder receives <i> g <sup> a </sup> </i>, generates a random <i> b </i> in <i> Z<sub>|g|</sub></i> and
sends <i> < g<sup>b</sup>, sign(skB, g<sup> b </sup>, g<sup>a</sup>) > </i>, and computes <i> (g <sup> a </sup>)<sup> b </sup> </i>. </li>
<li> The Initiator receives <i> < g<sup> b </sup> , sign(skB , g<sup> b</sup>, g<sup>a</sup> ) > </i>, verifies the signature, computes (g<sup> b </sup>)<sup> a </sup>, and sends <i> sign(skA , g <sup> a </sup>, g <sup>  b </sup> ) </i>.
<li> The Responder receives sign (skA, < g <sup> a </sup>, g <sup> b </sup> >), verifies the signature, and output <i> acc </i>. </li>
</ul>
#
 *)
  
 Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) .

(** Authentication is modeled as indistinguishability of two protocols, one in which the oracle reveals [TRue] if the given session is completed but no matching session (there exists an attack), and the one in which the oracle always reveals [FAlse]. 
We use [new] for [TRue] and [acc] for [FAlse] as those are of type message. *)
(** Protocol [Pi1] reveals [acc] always. *)

(** Frame [phi10] represents initial knowledge of the attacker. *)

Definition phi10 := [msg (G 0); msg (g 0); msg (pk 3); msg (pk 4)].
Definition mphi10 := (conv_mylist_listm phi10).
Definition grn (n:nat) := (exp (G 0) (g 0) (r n)).
Definition x1 := (f mphi10). 
Definition qa0 :=   (ifm ((eqm (to x1) (i 1)) & (eqm (act x1) new)) (grn 1) O).

(** Frame [phi11] represents attacker's knowledge during execution of the protocol. *)

Definition phi11 := phi10 ++ [msg qa0].
Definition mphi11 := (conv_mylist_listm phi11).
Definition x2 := (f mphi11).  
Definition qa1 :=    (ifm (eqm (to x2) (i 2)) (pair (grn 2) (sign (sk 4)  (pair (grn 2) x1))) O). 
 Definition qa0_s :=   (ifm ((eqm (to x1) (i 1)) & (eqm (act x1) new)) qa1 O).

(** Frame [phi12] also represents attackers's knowledge during execution of the protocol. *)
 Definition phi12:= phi11 ++ [msg qa0_s].

Definition mphi12 := (conv_mylist_listm phi12).
Definition x3 := (f mphi12).
  
Definition qa2 :=  (ifm (eqm (to x3) (i 1))& (ver (pk 4) ( (pi1 x2), (grn 1)) (pi2 x2)) (sign (sk 3) ( (grn 1), (pi1 (x2)))) O).

Definition qa1_s :=   (ifm (eqm (to x2) (i 2)) qa2 O). 
 Definition qa0_ss :=   (ifm ((eqm (to x1) (i 1)) & (eqm (act x1) new)) qa1_s O).
(** Frame [phi13] *) 
 Definition phi13 := phi12 ++ [msg qa0_ss].
 Definition mphi13 := (conv_mylist_listm phi13).
 Definition x4 := (f mphi13).
  
Definition qa3 :=  (ifm (eqm (to x4) (i 2)) & (ver (pk 3) (x1, (grn 2)) x4) acc O).
  
Definition qa2_s :=  (ifm (eqm (to x3) (i 1))& (ver (pk 4) ( (pi1 x2), (grn 1)) (pi2 x2)) qa3 O).

Definition qa1_ss :=   (ifm (eqm (to x2) (i 2)) qa2_s O). 
Definition qa0_sss :=   (ifm ((eqm (to x1) (i 1)) & (eqm (act x1) new)) qa1_ss O).
 (** if there is no matching session for a completed responder session, the oracle outputs [new] indicating that there is an attack, other wise outputs [acc] *) 
  Definition phi14 := phi13 ++ [msg qa0_sss]. 
 Definition mphi14 := (conv_mylist_listm phi13).
 Definition x5 := (f mphi14).
  Definition oracleop1 :=  (ifm (eqm (reveal x5) (i 2))& (notb (eqm x1 (grn 1))&(eqm (pi1(x2)) (grn 2)))  new acc ).

Definition qa3_s :=  (ifm (eqm (to x4) (i 2)) & (ver (pk 3) (x1, (grn 2)) x4) oracleop1 O).
  
Definition qa2_ss :=  (ifm (eqm (to x3) (i 1))& (ver (pk 4) ( (pi1 x2), (grn 1)) (pi2 x2)) qa3_s O).

Definition qa1_sss :=   (ifm (eqm (to x2) (i 2)) qa2_ss O). 
Definition qa0_ssss :=   (ifm ((eqm (to x1) (i 1)) & (eqm (act x1) new)) qa1_sss O).
 
(** Frame [phi13] attacker's knowledge at the end of the protocol. *)


Definition phi15 := phi14 ++ [msg qa0_ssss].

(** Protocol Pi2 reveals [new] if there is an attack, reveals [acc] otherwise. 

 All the frames in this protocol are equal to the frames in Pi1 except the last one and we define it here.
 *)

(** The oracle always outputs [acc] *)
  Definition oracleop2 :=  (ifm (eqm (reveal x5) (i 2))& (notb (eqm x1 (grn 1))&(eqm (pi1(x2)) (grn 2)))  acc acc ).

Definition qb3_s :=  (ifm (eqm (to x4) (i 2)) & (ver (pk 3) (x1, (grn 2)) x4) oracleop2 O).
  
Definition qb2_ss :=  (ifm (eqm (to x3) (i 1))& (ver (pk 4) ( (pi1 x2), (grn 1)) (pi2 x2)) qb3_s O).

Definition qb1_sss :=   (ifm (eqm (to x2) (i 2)) qb2_ss O). 
Definition qb0_ssss :=   (ifm ((eqm (to x1) (i 1)) & (eqm (act x1) new)) qb1_sss O).
 
Definition phi25 := phi14 ++ [msg qb0_ssss].

(** Proof of [phi13 #### phi23], where [####] is an equivalence relations on mylists. *)

Theorem IND_DH_AUTH:   phi15 #### phi25.

Proof. repeat unfold phi11, phi12, phi13, phi14, phi15, phi25. repeat  unfold qa0, qa1 , qa2, qa3,  qa0_s, qa1_s, qa2_s, qa3_s. simpl.
repeat unfold qa0_ss, qa0_sss, qa0_ssss, qb0_ssss, qa1_ss, qa1_sss, qb1_sss, qa2_s, qb2_ss, qa2_ss, qa3_s.
repeat unfold oracleop1, oracleop2.
repeat unfold qb3_s, qa1_s, qa3, qa2. 
assert (qa0_ssss # qb0_ssss).
repeat unfold qa0_ssss, qa1_sss, qa2_ss, qa3_s, qa3, qb0_ssss, qb1_sss, qb2_ss, qb3_s.
unfold oracleop1, oracleop2. 
pose proof( UFCMA 3 (x1 , grn 2) x4).
simpl in H.
rewrite H.
assert( (eqm x1 (grn 1)) ## (eqm  (pi1 (x1 , (grn 2))) (pi1 ((grn 1) , (pi1 x2))))).
repeat rewrite proj1. reflexivity.
assert( (eqm (pi1 x2) (grn 2)) ## (eqm (pi2 (grn 1, (pi1 x2))) (pi2 (x1, (grn 2))))).
repeat rewrite proj2. reflexivity.
repeat rewrite H0, H1.  
rewrite <- andB_assoc with (b1:=   (eqm (to x4) (i 2))) (b2:= (eqm (x1, grn 2) (grn 1, pi1 x2))) (b3:=  (ver (pk 3) (grn 1, pi1 x2) x4)). 
rewrite -> andB_comm with (b2:= (eqm (x1, grn 2) (grn 1, pi1 x2))) (b1:= (eqm (to x4) (i 2))).
rewrite -> andB_assoc with (b1:= (eqm (x1, grn 2) (grn 1, pi1 x2))). 
rewrite eqbrmsg_msg' with (m1:= (x1, grn 2)) (m2:= (grn 1, pi1 x2)) (b:=  ((eqm (to x4) (i 2)) & (ver (pk 3) (grn 1, pi1 x2) x4))) (m3:=  (ifm
                  (eqm (reveal x5) (i 2)) &
                  (notb
                     (eqm (pi1 (x1, grn 2)) (pi1 (grn 1, pi1 x2))) &
                     (eqm (pi2 (grn 1, pi1 x2)) (pi2 (x1, grn 2)))) new acc)) (m4:= O) (m:= (x1, grn 2)).
rewrite eqbrmsg_msg' with (m1:= (x1, grn 2)) (m2:= (grn 1, pi1 x2)) (b:=  ((eqm (to x4) (i 2)) & (ver (pk 3) (grn 1, pi1 x2) x4))) (m3:=  (ifm
                    (eqm (reveal x5) (i 2)) &
                    (notb
                       (eqm (pi1 (x1, grn 2)) (pi1 (grn 1, pi1 x2))) &
                       (eqm (pi2 (grn 1, pi1 x2)) (pi2 (x1, grn 2)))) acc acc)) (m4:= O) (m:= (x1, grn 2)).
simpl.
assert( (eqm (pi1 (grn 1, pi1 x2)) (pi1 (grn 1, pi1 x2))) ## TRue).
apply EQmsg with (x:=(pi1 (grn 1, pi1 x2))). reflexivity. repeat rewrite H2. 
repeat rewrite  IFTRUE_B.
assert( (eqm (pi2 (grn 1, pi1 x2)) (pi2 (grn 1, pi1 x2))) ## TRue).
apply EQmsg with (x:= (pi2 (grn 1, pi1 x2))). reflexivity.
repeat rewrite H3.
repeat rewrite IFTRUE_B.
repeat rewrite IFSAME_B.
repeat rewrite IFFALSE_M. reflexivity. try split; try reflexivity.
rewrite H. reflexivity. 
Qed.

End dh_auth.