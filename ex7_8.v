(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                   University of Missouri-Columbia.                   *)
(*                                                                      *)
(*                                                                      *)
(*                                                                      *)
(************************************************************************)

Load "ex7_7".
(**  This library defines a theorem that states, [if not(b) then x else y = if b then y else x ].
(*<!-- Of course, we use ## (resp. ##) for message (resp. Bool) in lieu of [=]. -->*) *)

Theorem Example16_B :  forall (n:nat) (b1 b2 :Bool), (ifb (notb  (Bvar n)) b1 b2) ## (ifb (Bvar n) b2 b1).
Proof.
intros.
unfold notb.
assert(H1: (ifb (ifb (Bvar n) FAlse TRue) b1 b2) ##
    (ifb (Bvar n) (  ifb FAlse b1 b2) ( ifb TRue b1 b2))).

apply IFMORPH_B2 .
rewrite H1.
rewrite IFFALSE_B.
rewrite IFTRUE_B.
reflexivity.
Qed.
Theorem Example16_M :  forall (n:nat) (m1 m2:message), (ifm (notb  (Bvar n)) m1 m2) # (ifm (Bvar n) m2 m1).
Proof.
intros.
unfold notb.
assert(H1: (ifm (ifb (Bvar n) FAlse TRue) m1 m2) #
    (ifm (Bvar n) (  ifm FAlse m1 m2) ( ifm TRue m1 m2))).

apply IFMORPH_M2 .
rewrite H1.
rewrite IFFALSE_M.
rewrite IFTRUE_M.
reflexivity.
Qed.
