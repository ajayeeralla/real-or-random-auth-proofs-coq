(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                   University of Missouri-Columbia.                   *)
(*                                                                      *)
(*                                                                      *)
(*                                                                      *)
(************************************************************************)

Load "ex7_1".

(** This library defines a theorem that states,[ [[ msg x]] ~ [[ msg y]] -> x # y.] *)
 
Theorem Example10_M: forall (x  F z : message), [msg x] ~ [msg (const F z )] -> x # (const F z) .
 Proof. 
intros.
simpl in H.
unfold const in H.
unfold const.
apply FUNCApp_const with (a := [msg F])(ml1 := ([msg x]))(ml2 := [msg F]) in H.
unfold const in H.
unfold app_mylist in H. 
apply FUNCApp_eqm with (p1 := 1) (p2:=2) in H.  
simpl in H.
unfold eqm_at_pos in H.
unfold chkmsg_os in H. unfold getelt_at_pos in H. 
simpl in H. 
unfold app_mylist in H.
restr_proj_in 1 H.
restr_proj_in 1 H.
assert (J:[bol (eqm F F) ] ~[bol TRue]) .
assert(K: (EQI_msg F F)).
reflexivity.
apply K.
assert (K:[bol (eqm x F)] ~[bol TRue]) .
apply EQI_trans with (ml2 := [bol (eqm F F)]).
assumption. assumption. assumption.
Qed.

(** The following theorem states that [x~f -> x=f] *)

Theorem Example10_B: forall (x  F z : Bool), [bol x] ~ [bol (const F z )] ->  x ## (const F  z) .
 Proof.
intros.
simpl in H.
unfold const in H.
unfold const.
apply FUNCApp_const with (a := [bol F])(ml1 := ([bol x]))(ml2 := [bol F]) in H.
unfold const in H.
simpl in H.
pose proof (FUNCApp_eqb).
apply FUNCApp_eqb with ( p1:=1)(p2:=2) in H.
unfold app_mylist in H.
unfold eqb_at_pos in H.
simpl in H.
restr_proj_in 1 H.
restr_proj_in 1 H.
assert (J:[bol (eqb F F) ] ~[bol TRue]) .
assert(K: (EQI_bol F F)).
reflexivity.
apply K.
assert (K:[bol (eqb x F)] ~[bol TRue]) .
apply EQI_trans with (ml2 := [bol (eqb F F)]).
apply H.
apply J.
apply K.
Qed.
