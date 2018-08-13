(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                   University of Missouri-Columbia.                   *)
(*                                                                      *)
(*                                                                      *)
(*                                                                      *)
(************************************************************************)

Load "morphisms".
(** This library defines equational theory and axioms. The axioms are written for [message] and [Bool] types. *)
   
(** * Equational theory *)

Section eqtheory.
  
Axiom proj1: forall (m1 m2 :message),  ((pi1 (pair m1 m2))  # m1).
Axiom proj2: forall (m1 m2 : message), ( (pi2 (pair m1 m2)) # m2) .
Axiom commexp: forall (x y g G: message), ( (exp G (exp G g x) y) # (exp G (exp G g y) x)).

End eqtheory.

(** * Axioms *)

(** Indistinguishability Axioms *)

(** [FUNCApp] *)

Section  Core_Axioms.
 
 (*************************************************************************************************)
Axiom FUNCApp_att4: forall {f} (p1 p2 p3 p4 : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos  p2 ml1)) (ostomsg (getelt_at_pos  p3 ml1)) (ostomsg (getelt_at_pos  p4 ml1)))] )
 ~ (ml2 ++ [ bol (f (ostomsg (getelt_at_pos  p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos  p3 ml2)) (ostomsg (getelt_at_pos p4 ml2)))] ).

Axiom FUNCApp_mconst: forall  {n} (m:message) (ml1 ml2 : mylist n), (const_msg m = true) -> (ml1 ~ ml2 )  -> (ml1 ++ [ msg  m] ) ~ (ml2 ++ [ msg m] ).

Axiom FUNCApp_bconst: forall  {n} (b:Bool) (ml1 ml2 : mylist n), (const_bol b = true)-> (ml1 ~ ml2 ) -> (ml1 ++ [ bol  b] )
 ~ (ml2 ++ [ bol b] ).

Axiom FUNCApp_f1: forall {f} (p:nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f (ostomsg (getelt_at_pos p ml1)))] ) ~ (ml2 ++ [ msg  (f (ostomsg (getelt_at_pos p ml2)))] ).

Axiom FUNCApp_f2b: forall {f} (p1 p2 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)))] ) ~ (ml2 ++ [ bol  (f (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)))] ).

Axiom FUNCApp_f2m: forall {f} (p1 p2 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)))] ) ~ (ml2 ++ [ msg (f (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)))] ).

Axiom FUNCApp_f3b: forall {f} (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)))] ) ~ (ml2 ++ [ bol  (f (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)))] ).

Axiom FUNCApp_f3bm: forall {f} (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f (ostobol (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)))] ) ~ (ml2 ++ [ msg  (f (ostobol (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)))] ).

Axiom FUNCApp_f3m: forall {f} (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)))] ) ~ (ml2 ++ [ msg  (f (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)))] ).

Axiom FUNCApp_f4b: forall {f} (p1 p2 p3 p4 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)) (ostomsg (getelt_at_pos p4 ml1)))] ) ~ (ml2 ++  [ bol  (f (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)) (ostomsg (getelt_at_pos p4 ml2)))] ).

Axiom FUNCApp_f4m: forall{f} (p1 p2 p3 p4 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)) (ostomsg (getelt_at_pos p4 ml1)))] ) ~ (ml2 ++  [ msg  (f (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)) (ostomsg (getelt_at_pos p4 ml2)))] ).

Axiom FUNCApp_g2: forall {g2} (p1 p2 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (g2 (ostobol (getelt_at_pos p1 ml1)) (ostobol (getelt_at_pos p2 ml1)))] ) ~ (ml2 ++ [ bol  (g2 (ostobol (getelt_at_pos p1 ml2)) (ostobol (getelt_at_pos p2 ml2)))] ).

Axiom FUNCApp_g3: forall {g3} (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (g3 (ostobol (getelt_at_pos p1 ml1)) (ostobol (getelt_at_pos p2 ml1)) (ostobol (getelt_at_pos p3 ml1)))] ) ~ (ml2 ++ [ bol  (g3 (ostobol (getelt_at_pos p1 ml2)) (ostobol (getelt_at_pos p2 ml2)) (ostobol (getelt_at_pos p3 ml2)))] ).
Axiom FUNCApp_sublist:  forall (m n:nat) {n1} (ml1 ml2:mylist n1), (ml1 ~ ml2) -> (ml1 ++ [msg (f  (sublist m n (conv_mylist_listm ml1)))]) ~ (ml2 ++ [msg (f (sublist m n (conv_mylist_listm ml2)))]).

(**************************************************************************************************)

Axiom FUNCApp_const: forall (n m :nat) (ml1 ml2: mylist n) (a: mylist m), (ml1 ~ ml2) -> (ml1 ++ (const  a ml1 )) ~ (ml2 ++ (const a ml2)).

Axiom FUNCApp_appelt:  forall (n p :nat) (ml1 ml2: mylist n), (ml1 ~ ml2) -> (ml1 ++ [getelt_at_pos  p ml1]  ) ~ (ml2 ++ [getelt_at_pos  p ml2]).

Axiom FUNCApp_eqm: forall (p1 p2:nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) -> (ml1 ++ ([ bol (eqm_at_pos  p1 p2 ml1) ])) ~ (ml2 ++ ([ bol (eqm_at_pos  p1 p2 ml2)])).
(*
Axiom FUNCApp_eqm1: forall (p p1 p2  :nat) {n}(ml1 ml2 :mylist n), (ml1 ~ ml2) -> (@insert_at_pos p  ( bol (eqm_at_pos (msg O) p1 p2 ml1)) n  ml1) ~ (@insert_at_pos p ( bol (eqm_at_pos (msg O) p1 p2 ml2)) n ml2). *)

Axiom FUNCApp_eqb: forall ( p1 p2:nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) ->  (ml1 ++  [ bol (eqb_at_pos  p1 p2 ml1)])  ~ (ml2 ++  [ bol (eqb_at_pos  p1 p2 ml2)])  .

(*Axiom FUNCApp_eqb1: forall ( p p1 p2:nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) ->  (@insert_at_pos p  ( bol (eqb_at_pos (bol TRue) p1 p2 ml1)) n  ml1)  ~ (@insert_at_pos p  ( bol (eqb_at_pos (bol TRue) p1 p2 ml1)) n  ml2) .*)

Axiom FUNCApp_negpos: forall (p :nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) -> (ml1 ++ (neg_at_pos p ml1)) ~ (ml2 ++ (neg_at_pos p ml2)).

Axiom FUNCApp_ifmnespair : forall ( p1 p2 p3 p4 : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> (ml1 ++ [msg (ifm_nespair  p1 p2 p3 p4 ml1)]) ~(ml2 ++ [msg (ifm_nespair  p1 p2 p3 p4 ml2)]).

Axiom FUNCApp_ifmpair: forall ( p1 p2 p3 p4  : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> (ml1 ++ [msg (ifm_pair  p1 p2 p3 p4 ml1)]) ~ (ml2 ++ [ msg (ifm_pair p1 p2 p3 p4 ml2)]). 

(*Axiom FUNCApp_expatpos: forall (n p p1 p2 p3 : nat) (ml1 ml2 : mylist n), (ml1 ~ ml2) -> ( app_elt_pos (msg (exp_at_pos (msg O) p1 p2 p3  ml1)) p ml1 ) ~ ( app_elt_pos (msg (exp_at_pos (msg O) p1 p2 p3  ml2)) p ml2 ) .  *)

Axiom FUNCApp_expatpos: forall (p1 p2 p3 : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> ( ml1 ++ [msg (exp_at_pos  p1 p2 p3  ml1)]) ~ ( ml2 ++ [msg (exp_at_pos  p1 p2 p3  ml2)]) .
(*
Axiom FUNCApp_expatpos1: forall (p p1 p2 p3 : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> ( @insert_at_pos p  (msg (exp_at_pos (msg O) p1 p2 p3  ml1)) n ml1 ) ~ ( @insert_at_pos p  (msg (exp_at_pos (msg O) p1 p2 p3  ml2)) n ml2 ).
*)
Axiom FUNCApp_att : forall {n} (ml1 ml2: mylist n) (l1 l2 :list message ), (ml1 ~ ml2) -> ([msg (f l1)] ++ ml1) ~ ([msg (f l2)] ++ ml2).

Axiom FUNCApp_reveal:  forall ( p:nat) {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg (reveal_at_pos p ml1)] ++ml1   ) ~ ([msg (reveal_at_pos p ml2)] ++ml2 ).

Axiom FUNCApp_to:  forall (p:nat) {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg (to_at_pos p ml1)] ++ ml1)  ~ ([msg (to_at_pos p ml2)] ++ ml2).

Axiom FUNCApp_act:  forall (p:nat) {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg (act_at_pos p ml1)] ++ ml1)  ~ ([msg (act_at_pos p ml2)] ++ ml2).

Axiom FUNCApp_new : forall {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg new ] ++ ml1) ~ ([msg new ] ++ ml2).

Axiom FUNCApp_O : forall {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ( ml1 ++ [msg O]) ~ (ml2 ++ [msg O]).

Axiom FUNCApp_acc : forall {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ( ml1 ++ [msg acc]) ~ (ml2 ++ [msg acc]).

Axiom FUNCApp_session : forall ( m: nat ) {n} (ml1 ml2 : mylist m) , (ml1 ~ ml2) -> ([msg (i n) ] ++ ml1) ~ ([msg (i n) ] ++ ml2).


Axiom restr_sublis : forall {m} {n} (l1 l2 : mylist m) (l1' l2': mylist n) ,  l1 ~ l2 -> (andb (checksublis (conv_mylist_listos l1') l1) (checksublis (conv_mylist_listos l2') l2)  = true ) -> (sublisindcs (conv_mylist_listos l1') l1) = (sublisindcs (conv_mylist_listos l2') l2)-> l1' ~ l2'.

Axiom funapptrm : forall {m} (t1 t2 : oursum) (l1 l2 : mylist m),  l1 ~ l2 -> (topsyos_beq t1 t2 = true ) -> (andb (checksublis (subtrms_os' t1)  l1) (checksublis (subtrms_os' t2) l2) = true) ->  (sublisindcs (subtrms_os' t1) l1) = (sublisindcs (subtrms_os' t2) l2) -> (l1 ++ [ t1]) ~ (l2 ++ [ t2]).

Axiom FUNCApp_andB : forall (p1 p2 :nat) {m} (ml1 ml2 : mylist m), (ml1 ~ ml2) -> (ml1 ++ [bol (andB_at_pos p1 p2 ml1)]) ~  (ml2 ++ [bol (andB_at_pos p1 p2 ml2)]).

Axiom FUNCApp_notB : forall (p :nat) {m} (ml1 ml2:mylist m), (ml1 ~ ml2) -> (ml1 ++ [bol (notB_at_pos  p ml1)]) ~ (ml2 ++ [bol (notB_at_pos p ml2)]).

Axiom FUNCApp_m : forall (p :nat) {m} (ml1 ml2:mylist m), (ml1 ~ ml2) -> ( [ msg (m_at_pos  p ml1)] ++ ml1) ~  (  [msg (m_at_pos  p ml2) ] ++ ml2).

Axiom FUNCApp_elt :   forall (p p1  :nat) {m} (ml1 ml2:mylist m), (ml1~ml2) ->  (ml1 ++ [getelt_at_pos  p1 ml1 ] ) ~ (ml2 ++ [  getelt_at_pos p1 ml2]).

Axiom FUNCApp_pair: forall (p1 p2 :nat) {m} (ml1 ml2 : mylist m), (ml1 ~ ml2) -> (ml1++ [msg (pair (ostomsg (getelt_at_pos p1 ml1)) (ostomsg ( getelt_at_pos p2 ml1))) ]) ~ (ml2 ++ [ msg  (pair (ostomsg (getelt_at_pos p1 ml2)) (ostomsg ( getelt_at_pos p2 ml2 )))]).
 
Axiom FUNCApp_pi1: forall (p :nat)  {m} (ml1 ml2 : mylist m), (ml1 ~ ml2) -> ( [ msg (pi1 (ostomsg (getelt_at_pos p ml1)))] ++ ml1) ~  ( [ msg (pi1 (ostomsg (getelt_at_pos p ml2)))] ++ ml2).

Axiom FUNCApp_pi2: forall (p :nat)  {m} (ml1 ml2 : mylist m), (ml1 ~ ml2) -> ( [ msg (pi2 (ostomsg (getelt_at_pos p ml1)))] ++ ml1 ) ~  ( [ msg (pi2 (ostomsg (getelt_at_pos p ml2)))] ++ ml2).

 
(** [RESTR] *)

(** Indistinguishability is closed under projections *)

Axiom RESTR_proj : forall ( p :nat) {m} (ml1 ml2 :mylist m), ml1 ~ ml2 -> (proj_at_pos p ml1) ~ (proj_at_pos p ml2).

Axiom RESTR_dropls: forall {n} (ml1 ml2: mylist n), ml1 ~ ml2 -> (droplastsec ml1) ~ (droplastsec ml2).

Axiom RESTR_dropone: forall {n} (ml1 ml2: mylist n), ml1 ~ ml2 -> (dropone ml1) ~ (dropone ml2).

(** Indistinguishability is closed under permutations *)

Axiom RESTR_swap : forall (p1 p2 : nat) {n} (ml1 ml2 : mylist n), ml1~ ml2 -> (swap_mylist p1 p2 ml1) ~ (swap_mylist p1 p2 ml2).

Axiom RESTR_swapls: forall {n1 n2} (ml1 ml2 : mylist n1) (ml3 ml4 :mylist n2) , (ml1 ++ ml3) ~ (ml2 ++ ml4) -> (ml3 ++ ml1) ~ (ml4 ++ ml2).
 

(********************~ closed under permutations **********************)
(*
Axiom RESTR_SWAP : forall (p1 p2 : nat) {n} (ml1 ml2 : mylist n), ml1~ ml2 -> (swap_mylist p1 p2 ml1) ~ (swap_mylist p1 p2 ml2).
Axiom RESTR_rev: forall (n:nat) (ml1 ml2: mylist n) , ml1 ~ ml2 -> (reverse ml1) ~ (reverse ml2).*)

Axiom RESTR2 : forall (n1 n2 n3 :nat) (l1 l1' : mylist n1) (l2 l2' : mylist n2) (l3 l3' : mylist n3) (x1 x2 y1 y2 : oursum), (l1 ++ [x1] ++ l2 ++ [x2] ++ l3) ~ (l1' ++ [y1] ++ l2' ++ [y2] ++ l3') -> (l1 ++ [x2] ++ l2 ++ [x1] ++ l3) ~ (l1' ++ [y2] ++ l2' ++ [y1] ++ l3').

(** [IFDIST] *)

Axiom TFDIST: not ([bol TRue]~[bol FAlse]).

(** Axioms for [if_then_else] function symbol. *)

(** [IFSAME] *)

Axiom IFSAME_M: forall (b:Bool) (x : message), (ifm b x x) # x.

Axiom IFSAME_B: forall (b:Bool) (b1 : Bool),  (ifb b b1 b1) ## b1.

(** [IFEVAL] *)

Axiom IFEVAL_B : forall (b1 b2 : Bool)(n:nat),  (ifb (Bvar n) b1 b2) ## (ifb (Bvar n) ([n := TRue] b1) ([n := FAlse] b2)).

Axiom IFEVAL_M : forall (t1 t2 : message) (n:nat),  (ifm (Bvar n) t1 t2) #(ifm (Bvar n) ((n := TRue) t1) ((n := FAlse) t2)).

Axiom IFEVAL_B' : forall (b b1 b2 : Bool),  (ifb b b1 b2) ## (ifb b (subbol_bol' b TRue b1) (subbol_bol' b FAlse b2)).

Axiom IFEVAL_M' : forall (b:Bool)(t1 t2  : message),  (ifm b t1 t2) #(ifm b (subbol_msg' b TRue t1) (subbol_msg' b FAlse t2)).

(** [IFTRue] *)

Axiom IFTRUE_M : forall (x y : message),  (ifm TRue x y) # x .

Axiom IFTRUE_B : forall (b1 b2 : Bool), (ifb TRue b1 b2) ## b1.

(** [IFFAlse] *)

Axiom IFFALSE_M: forall (x y : message), (ifm FAlse x y) # y.

Axiom IFFALSE_B: forall (b1 b2 : Bool),  (ifb FAlse b1 b2) ## b2.

(** [Fresh] *)

Axiom FRESHNEQ: forall (n : nat) (m : message), ((clos_msg m) = true)/\ ( (Fresh [n] [msg m]) = true) ->[bol (eqm (N n) m)]~ [bol FAlse] .

Axiom FRESHIND: forall (n n1 n2:nat) (v w: mylist n), ((clos_mylist (v++w)) = true) /\ ( (Fresh [ n1] (v++w)) = true) /\ ( (Fresh [ n2] (v++w)) = true) /\  (v ~ w) <-> ((msg (r n1) ) +++ v) ~ (( msg (r n2)) +++w ) .

Axiom FRESHIND_rs : forall (n n1 n2:nat) (v w: mylist n), ((clos_mylist (v++w)) = true) /\ ( (Fresh [ n1] (v++w)) = true) /\ ( (Fresh [ n2] (v++w)) = true) /\  (v ~ w) <-> ((msg  (N n1)) +++ v) ~ (( msg  (N n2)) +++w ) .

(** [DDH] assumption:
[[
    Fresh [n;n1;n2;n3]-> [G(n); g(n);g(n)^(r (n1));g(n)^(r (n2)); g(n)^(r (n1))(r (n2))] ~[G(n); g(n);g(n)^(r (n1));g(n)^(r (n2)); g(n)^(r (n3))]
]] 
*)
     
Axiom DDH : forall (n n1 n2 n3: nat),  (Fresh [ n ; n1 ;  n2  ; n3 ] []) = true-> 
[ msg (G n) ; msg (g n) ; msg (exp (G n) (g n) (r  n1)) ; msg (exp (G n) (g n) (r  n2)) ; msg (exp (G n) (exp (G n) (g n) (r  n1)) (r  n2))]
~ [msg (G n) ; msg (g n) ; msg (exp (G n) (g n) (r  n1)) ; msg (exp (G n) (g n) (r n2)) ; msg (exp (G n) (g n) (r n3))] .

(** [IFBRANCH] *)

Axiom IFBRANCH_M: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x x' y y':message), (ml1 ++ [ bol b ; msg x] ) ~  ( ml2 ++ [ bol b'; msg x'])  ->  (ml1 ++ [bol b ; msg y ] ) ~( ml2 ++ [bol b' ; msg y'])
-> (ml1 ++ [bol b ;msg (ifm b x y)])~ ( ml2 ++ [bol b' ; msg (ifm b' x' y')]).

Axiom IFBRANCH_B: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(b1 b1' b2 b2':Bool), (ml1 ++ [bol b ;bol b1]) ~ ( ml2 ++ [bol b' ; bol b1'])  ->  (ml1 ++ [ bol b; bol b2]) ~( ml2 ++ [bol b'; bol b2'])
-> (ml1 ++ [ bol b ;bol (ifb b b1 b2)])~ (  ml2 ++ [bol b' ; bol (ifb b' b1' b2')] ).

Axiom IFBRANCH_M1: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x x' y y':message), (ml1 ++ [ bol b ; msg x] ) ~  ( ml2 ++ [ bol b'; msg x'])  ->  (ml1 ++ [bol b ; msg y ] ) ~( ml2 ++ [bol b' ; msg y']) -> (ml1 ++  [ msg (ifm b x y)])~ ( ml2 ++ [ msg (ifm b' x' y')]).


Axiom IFBRANCH_M2: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' y1 y1' y2 y2' :message), (ml1 ++ [ bol b ; msg x1; msg x2] ) ~  ( ml2 ++ [ bol b'; msg x1' ; msg x2'])  ->  (ml1 ++ [bol b ; msg y1 ; msg y2 ] ) ~( ml2 ++ [bol b' ; msg y1'; msg y2']) 
                                                                                     -> (ml1 ++  [ msg (ifm b x1 y1) ; msg (ifm b x2 y2) ])~ ( ml2 ++ [ msg (ifm b' x1' y1') ; msg (ifm b' x2' y2')]).


Axiom IFBRANCH_M3: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' y1 y1' y2 y2' y3 y3' :message), (ml1 ++ [ bol b ; msg x1; msg x2 ; msg x3] ) ~  ( ml2 ++ [ bol b'; msg x1' ; msg x2' ; msg x3'])  ->  (ml1 ++ [bol b ; msg y1 ; msg y2 ; msg y3 ] ) ~( ml2 ++ [bol b' ; msg y1'; msg y2' ; msg y3'])                                                                                               -> (ml1 ++  [ msg (ifm b x1 y1) ; msg (ifm b x2 y2) ; msg (ifm b x3 y3) ])~ ( ml2 ++ [ msg (ifm b' x1' y1') ; msg (ifm b' x2' y2') ; msg (ifm b' x3' y3')]).

Axiom IFBRANCH_M4: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' x4 x4' y1 y1' y2 y2' y3 y3' y4 y4' :message), (ml1 ++ [ bol b ; msg x1; msg x2 ; msg x3; msg x4] ) ~  ( ml2 ++ [ bol b'; msg x1' ; msg x2' ; msg x3'; msg x4'])  ->  (ml1 ++ [bol b ; msg y1 ; msg y2 ; msg y3; msg y4 ] ) ~( ml2 ++ [bol b' ; msg y1'; msg y2' ; msg y3'; msg y4'])  -> (ml1 ++  [ msg (ifm b x1 y1) ; msg (ifm b x2 y2) ; msg (ifm b x3 y3) ; msg (ifm b x4 y4) ])~ ( ml2 ++ [ msg (ifm b' x1' y1') ; msg (ifm b' x2' y2') ; msg (ifm b' x3' y3') ;  msg (ifm b' x4' y4')]).

Axiom IFBRANCH_M5: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' y1 y1' y2 y2' y3 y3' y4 y4' y5 y5' :message), (ml1 ++ [ bol b ; msg x1; msg x2 ; msg x3; msg x4 ; msg x5] ) ~  ( ml2 ++ [ bol b'; msg x1' ; msg x2' ; msg x3'; msg x4'; msg x5'])  ->  (ml1 ++ [bol b ; msg y1 ; msg y2 ; msg y3; msg y4; msg y5 ] ) ~( ml2 ++ [bol b' ; msg y1'; msg y2' ; msg y3'; msg y4'; msg y5'])  -> (ml1 ++  [ msg (ifm b x1 y1) ; msg (ifm b x2 y2) ; msg (ifm b x3 y3) ; msg (ifm b x4 y4); msg (ifm b x5 y5) ])~ ( ml2 ++ [ msg (ifm b' x1' y1') ; msg (ifm b' x2' y2') ; msg (ifm b' x3' y3') ;  msg (ifm b' x4' y4'); msg (ifm b' x5' y5')]).

Axiom IFBRANCH_M7: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' x6 x6' x7 x7' y1 y1' y2 y2' y3 y3' y4 y4' y5 y5' y6 y6' y7 y7' :message), (ml1 ++ [ bol b ; msg x1; msg x2 ; msg x3; msg x4 ; msg x5; msg x6 ; msg x7] ) ~  ( ml2 ++ [ bol b'; msg x1' ; msg x2' ; msg x3'; msg x4'; msg x5' ; msg x6' ; msg x7'])  ->  (ml1 ++ [bol b ; msg y1 ; msg y2 ; msg y3; msg y4; msg y5; msg y6 ; msg y7 ] ) ~( ml2 ++ [bol b' ; msg y1'; msg y2' ; msg y3'; msg y4'; msg y5'; msg y6' ; msg y7'])  -> (ml1 ++  [ msg (ifm b x1 y1) ; msg (ifm b x2 y2) ; msg (ifm b x3 y3) ; msg (ifm b x4 y4); msg (ifm b x5 y5); msg (ifm b x6 y6); msg (ifm b x7 y7) ])~ ( ml2 ++ [ msg (ifm b' x1' y1') ; msg (ifm b' x2' y2') ; msg (ifm b' x3' y3') ;  msg (ifm b' x4' y4'); msg (ifm b' x5' y5'); msg (ifm b' x6' y6'); msg (ifm b' x7' y7')]).


End Core_Axioms.

(** * Auxilary Axioms *)
Section aux_axioms.

(** Equality ([Bool] or [message]) is closed under substitution. *)

Axiom Forall_ELM_EVAL_M: forall (x:Bool) (n:nat) (t1 t2 :message), ( t1 # t2 ) ->  ((( n:=x )t1) # ((n:=x)t2)).
Axiom Forall_ELM_EVAL_B: forall (b:Bool) (n:nat) (b1 b2 :Bool), (  b1 ## b2 ) ->  ( ([n:=b] b1) ## ([n:=b] b2)).

Axiom Forall_ELM_EVAL_M1: forall (x:message) (n:nat) (t1 t2 :message), (t1 # t2 ) ->  ({{n:=x}} t1 # {{n:=x}}t2).
Axiom Forall_ELM_EVAL_B1: forall (b:message) (n:nat) (b1 b2 :Bool), ( b1 ## b2 ) ->  ( [[n:=b]] b1 ## [[n:=b]] b2).

Axiom Forall_ELM_EVAL_M2: forall (x:Bool) (n:nat) (t1 t2 :message), (t1 # t2)  ->  ( (( n:=x )t1) # ((n:=x)t2 )).
Axiom Forall_ELM_EVAL_B2: forall (b:Bool) (n:nat) (b1 b2 :Bool), (b1 ## b2)  ->   ( [n:=b] b1 ## [n:=b] b2).

Axiom Forall_ELM_EVAL_M3: forall (x:message) (n:nat) (t1 t2 :message),  ( t1 # t2)  ->  ( {{n:=x}} t1  # {{n:=x}}t2).
Axiom Forall_ELM_EVAL_B3: forall (b:message) (n:nat) (b1 b2 :Bool), ( b1 ## b2) ->   ( [[n:=b]] b1 ## [[n:=b]] b2).
 
(** There always exists a natural number which doesn't occur in lists of terms. *)

Axiom existsn_mylist: forall (m1 m2 :nat) (nl : ilist nat m1)(bl:mylist m2), exists n , (notoccur_nlist n nl = true) /\ (notoccur_mylist n bl = true).
Axiom existsn_Blist : forall (m1 m2 :nat) (nl : ilist nat m1)(bl:ilist Bool m2), exists n , (notoccur_nlist n nl = true) /\ (notoccur_blist n bl = true).
Axiom existsn_Mlist: forall (m1 m2 :nat) (nl : ilist nat m1)(ml:ilist message m2), exists n , (notoccur_nlist n nl = true) /\ (notoccur_mlist n ml = true).

(** Substitution inside substitution. *)

Axiom notocc_bolmm: forall (n1 n2 : nat) (b: Bool) (m1 m2 : message), (notoccur_msg n1 m2) = true -> ( n1 :=  b)  ((submsg_msg n2 m1)  m2) = (submsg_msg n2 (( n1 := b) m1)) m2 .


Axiom notocc_bolbb : forall  (n1 n2 :nat) (b b1 b2:Bool), (notoccur_bol n1 b2) = true -> ([ n1 :=  b]  [ n2 := b1]  b2)  =    ( [ n2 := ([n1:=b] b1)]  b2) .


Axiom notocc_bolmb : forall (n1 n2 :nat) (b  b1:Bool) (m:message),(notoccur_bol n1 b1) = true -> ([ n1 :=  b]  [[ n2 := m]]  b1)  =    ( [[ n2 := ((n1 := b) m)]]  b1).


Axiom notocc_bolbm : forall (n1 n2 :nat) (b  b1:Bool) (m:message),(notoccur_msg n1 m) = true -> ( ( n1 :=  b)  (( n2 := b1) m)  =    ( ( n2 := ([n1 := b] b1))  m)).

 (** Trivially sound axioms. *)

Axiom  invarsub_Bmsg : forall(n:nat)(t:message), ((n:= (Bvar n))t = t).
Axiom invarsub_BBool: forall(n:nat)(b:Bool), ([n:=(Bvar n)] b) = b.
Axiom invarsub_mBool : forall(n:nat)(b: Bool), ([[n:= (Mvar n)]] b) = b. 
Axiom invarsub_mmsg : forall(n:nat)(t: message),{{n:= (Mvar n)}} t = t. 

End aux_axioms.
