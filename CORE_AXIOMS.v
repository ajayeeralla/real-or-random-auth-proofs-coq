Load "IND_MORPHISMS".

   
  

 (***********Equational theory for DDH**************************************)
(**************************************************************************)



Section eqtheory.

Axiom proj1: forall (m1 m2 :message),  ((pi1 (pair m1 m2))  # m1).
Axiom proj2: forall (m1 m2 : message), ( (pi2 (pair m1 m2)) # m2) .
Axiom commexp: forall (x y g G: message), ( (exp G (exp G g x) y) # (exp G (exp G g y) x)).


End eqtheory.


(***********Indistinguishability Axioms*******************************************)
(*********************************************************************************)
(*********************FUNCApp***************************************************)
(*******************************************************************************)
 Section  Core_Axioms.
Variable fmb4 : message -> message -> message -> message -> Bool.
Variable fm: message.
Variable fb: Bool.
Variable f1 : message  -> message.
Variable f2b : message  -> message -> Bool.
Variable f2m : message ->  message -> message.
Variable f3b: message -> message -> message -> Bool.
Variable f3bm: Bool -> message -> message -> message.
Variable f3m : message -> message -> message -> message .
Variable f4b: message -> message -> message -> message -> Bool.
Variable f4m: message -> message -> message -> message -> message.
Variable g2: Bool -> Bool -> Bool.
Variable g3 : Bool -> Bool -> Bool -> Bool.
 (*************************************************************************************************)
Axiom FUNCApp_att4: forall (p1 p2 p3 p4 : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol (fmb4 (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos  p2 ml1)) (ostomsg (getelt_at_pos  p3 ml1)) (ostomsg (getelt_at_pos  p4 ml1)))] )
 ~ (ml2 ++ [ bol (fmb4 (ostomsg (getelt_at_pos  p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos  p3 ml2)) (ostomsg (getelt_at_pos p4 ml2)))] ).

Axiom FUNCApp_mconst: forall  {n} (m:message) (ml1 ml2 : mylist n), (const_msg m = true) -> (ml1 ~ ml2 )  -> (ml1 ++ [ msg  m] ) ~ (ml2 ++ [ msg m] ).
Axiom FUNCApp_bconst: forall  {n} (b:Bool) (ml1 ml2 : mylist n), (const_bol b = true)-> (ml1 ~ ml2 ) -> (ml1 ++ [ bol  b] )
 ~ (ml2 ++ [ bol b] ).

Axiom FUNCApp_f1: forall (p:nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f1 (ostomsg (getelt_at_pos p ml1)))] ) ~ (ml2 ++ [ msg  (f1 (ostomsg (getelt_at_pos p ml2)))] ).


Axiom FUNCApp_f2b: forall (p1 p2 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (f2b (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)))] ) ~ (ml2 ++ [ bol  (f2b (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)))] ).

Axiom FUNCApp_f2m: forall (p1 p2 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f2m (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)))] ) ~ (ml2 ++ [ msg (f2m (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)))] ).


 Axiom FUNCApp_f3b: forall (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (f3b (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)))] ) ~ (ml2 ++ [ bol  (f3b (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)))] ).

 Axiom FUNCApp_f3bm: forall (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f3bm (ostobol (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)))] ) ~ (ml2 ++ [ msg  (f3bm (ostobol (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)))] ).

 Axiom FUNCApp_f3m: forall (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f3m (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)))] ) ~ (ml2 ++ [ msg  (f3m (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)))] ).

Axiom FUNCApp_f4b: forall (p1 p2 p3 p4 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (f4b (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)) (ostomsg (getelt_at_pos p4 ml1)))] ) ~ (ml2 ++  [ bol  (f4b (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)) (ostomsg (getelt_at_pos p4 ml2)))] ).

Axiom FUNCApp_f4m: forall (p1 p2 p3 p4 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ msg  (f4m (ostomsg (getelt_at_pos p1 ml1)) (ostomsg (getelt_at_pos p2 ml1)) (ostomsg (getelt_at_pos p3 ml1)) (ostomsg (getelt_at_pos p4 ml1)))] ) ~ (ml2 ++  [ msg  (f4m (ostomsg (getelt_at_pos p1 ml2)) (ostomsg (getelt_at_pos p2 ml2)) (ostomsg (getelt_at_pos p3 ml2)) (ostomsg (getelt_at_pos p4 ml2)))] ).
Axiom FUNCApp_g2: forall (p1 p2 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (g2 (ostobol (getelt_at_pos p1 ml1)) (ostobol (getelt_at_pos p2 ml1)))] ) ~ (ml2 ++ [ bol  (g2 (ostobol (getelt_at_pos p1 ml2)) (ostobol (getelt_at_pos p2 ml2)))] ).


 Axiom FUNCApp_g3: forall (p1 p2 p3 :nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2 ) -> (ml1 ++ [ bol  (g3 (ostobol (getelt_at_pos p1 ml1)) (ostobol (getelt_at_pos p2 ml1)) (ostobol (getelt_at_pos p3 ml1)))] ) ~ (ml2 ++ [ bol  (g3 (ostobol (getelt_at_pos p1 ml2)) (ostobol (getelt_at_pos p2 ml2)) (ostobol (getelt_at_pos p3 ml2)))] ).
Axiom FUNCApp_sublist:  forall (m n:nat) {n1} (ml1 ml2:mylist n1), (ml1 ~ ml2) -> (ml1 ++ [msg (f  (sublist m n (conv_mylist_listm ml1)))]) ~ (ml2 ++ [msg (f (sublist m n (conv_mylist_listm ml2)))]).

(**************************************************************************************************)
Axiom FUNCApp_const: forall (n m :nat) (ml1 ml2: mylist n) (a: mylist m), (ml1 ~ ml2) -> (ml1 ++ (const  a ml1 )) ~ (ml2 ++ (const a ml2)).

Axiom FUNCApp_appelt:  forall (n p :nat) (ml1 ml2: mylist n), (ml1 ~ ml2) -> (ml1 ++ [getelt_at_pos  p ml1]  ) ~ (ml2 ++ [getelt_at_pos  p ml2]).

Axiom FUNCApp_EQ_M: forall (p1 p2:nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) -> (ml1 ++ ([ bol (EQ_M_at_pos  p1 p2 ml1) ])) ~ (ml2 ++ ([ bol (EQ_M_at_pos  p1 p2 ml2)])).
(**
Axiom FUNCApp_EQ_M1: forall (p p1 p2  :nat) {n}(ml1 ml2 :mylist n), (ml1 ~ ml2) -> (@insert_at_pos p  ( bol (EQ_M_at_pos (msg O) p1 p2 ml1)) n  ml1) ~ (@insert_at_pos p ( bol (EQ_M_at_pos (msg O) p1 p2 ml2)) n ml2). **)
Axiom FUNCApp_EQ_B: forall ( p1 p2:nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) ->  (ml1 ++  [ bol (EQ_B_at_pos  p1 p2 ml1)])  ~ (ml2 ++  [ bol (EQ_B_at_pos  p1 p2 ml2)])  .

(**Axiom FUNCApp_EQ_B1: forall ( p p1 p2:nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) ->  (@insert_at_pos p  ( bol (EQ_B_at_pos (bol TRue) p1 p2 ml1)) n  ml1)  ~ (@insert_at_pos p  ( bol (EQ_B_at_pos (bol TRue) p1 p2 ml1)) n  ml2) .**)

Axiom FUNCApp_negpos: forall (p :nat) {n} (ml1 ml2: mylist n), (ml1 ~ ml2) -> (ml1 ++ (neg_at_pos p ml1)) ~ (ml2 ++ (neg_at_pos p ml2)).

Axiom FUNCApp_ifmnespair : forall ( p1 p2 p3 p4 : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> (ml1 ++ [msg (ifm_nespair  p1 p2 p3 p4 ml1)]) ~(ml2 ++ [msg (ifm_nespair  p1 p2 p3 p4 ml2)]).

Axiom FUNCApp_ifmpair: forall ( p1 p2 p3 p4  : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> (ml1 ++ [msg (ifm_pair  p1 p2 p3 p4 ml1)]) ~ (ml2 ++ [ msg (ifm_pair p1 p2 p3 p4 ml2)]). 

(*Axiom FUNCApp_expatpos: forall (n p p1 p2 p3 : nat) (ml1 ml2 : mylist n), (ml1 ~ ml2) -> ( app_elt_pos (msg (exp_at_pos (msg O) p1 p2 p3  ml1)) p ml1 ) ~ ( app_elt_pos (msg (exp_at_pos (msg O) p1 p2 p3  ml2)) p ml2 ) .  *)

Axiom FUNCApp_expatpos: forall (p1 p2 p3 : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> ( ml1 ++ [msg (exp_at_pos  p1 p2 p3  ml1)]) ~ ( ml2 ++ [msg (exp_at_pos  p1 p2 p3  ml2)]) .
(**
Axiom FUNCApp_expatpos1: forall (p p1 p2 p3 : nat) {n} (ml1 ml2 : mylist n), (ml1 ~ ml2) -> ( @insert_at_pos p  (msg (exp_at_pos (msg O) p1 p2 p3  ml1)) n ml1 ) ~ ( @insert_at_pos p  (msg (exp_at_pos (msg O) p1 p2 p3  ml2)) n ml2 ).
**)



Axiom FUNCApp_att : forall {n} (ml1 ml2: mylist n) (l1 l2 :list message ), (ml1 ~ ml2) -> ([msg (f l1)] ++ ml1) ~ ([msg (f l2)] ++ ml2).

Axiom FUNCApp_reveal:  forall ( p:nat) {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg (reveal_at_pos p ml1)] ++ml1   ) ~ ([msg (reveal_at_pos p ml2)] ++ml2 ).

Axiom FUNCApp_to:  forall (p:nat) {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg (to_at_pos p ml1)] ++ ml1)  ~ ([msg (to_at_pos p ml2)] ++ ml2).

Axiom FUNCApp_act:  forall (p:nat) {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg (act_at_pos p ml1)] ++ ml1)  ~ ([msg (act_at_pos p ml2)] ++ ml2).

Axiom FUNCApp_new : forall {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ([msg new ] ++ ml1) ~ ([msg new ] ++ ml2).
Axiom FUNCApp_O : forall {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ( ml1 ++ [msg O]) ~ (ml2 ++ [msg O]).
Axiom FUNCApp_acc : forall {n} (ml1 ml2 : mylist n) , (ml1 ~ ml2) -> ( ml1 ++ [msg acc]) ~ (ml2 ++ [msg acc]).
Axiom FUNCApp_session : forall ( m: nat ) {n} (ml1 ml2 : mylist m) , (ml1 ~ ml2) -> ([msg (i n) ] ++ ml1) ~ ([msg (i n) ] ++ ml2).
(**
Axiom FUNCApp_andB1: forall (p p1 p2:nat)  {n}(ml1 ml2: mylist n), (ml1 ~ ml2) ->  (@insert_at_pos p  ( bol (andB_at_pos (msg O) p1 p2 ml1)) n  ml1)  ~ (@insert_at_pos p  ( bol (andB_at_pos (msg O) p1 p2 ml1)) n  ml2) .
**)
Axiom FUNCApp_andB : forall (p1 p2 :nat) {m} (ml1 ml2 : mylist m), (ml1 ~ ml2) -> (ml1 ++ [bol (andB_at_pos p1 p2 ml1)]) ~  (ml2 ++ [bol (andB_at_pos p1 p2 ml2)]).
Axiom FUNCApp_notB : forall (p :nat) {m} (ml1 ml2:mylist m), (ml1 ~ ml2) -> (ml1 ++ [bol (notB_at_pos  p ml1)]) ~ (ml2 ++ [bol (notB_at_pos p ml2)]).
Axiom FUNCApp_m : forall (p :nat) {m} (ml1 ml2:mylist m), (ml1 ~ ml2) -> ( [ msg (m_at_pos  p ml1)] ++ ml1) ~  (  [msg (m_at_pos  p ml2) ] ++ ml2).
(**
Axiom FUNCApp_exptrm : forall (p n n1:nat) {m} (ml1 ml2:mylist m), (ml1~ml2) -> ((occexp_in_mylist n n1 ml1) = true) ->  ((occexp_in_mylist n n1 ml2) = true)  -> (@insert_at_pos p ( msg (exp (G n) (g n) (r n1))) m ml1) ~ (@insert_at_pos p ( msg (exp (G n) (g n) (r n1))) m ml2).
**)
Axiom FUNCApp_elt :   forall (p p1  :nat) {m} (ml1 ml2:mylist m), (ml1~ml2) ->  (ml1 ++ [getelt_at_pos  p1 ml1 ] ) ~ (ml2 ++ [  getelt_at_pos p1 ml2]).
Axiom FUNCApp_pair: forall (p1 p2 :nat) {m} (ml1 ml2 : mylist m), (ml1 ~ ml2) -> (ml1++ [msg ( ostomsg (getelt_at_pos p1 ml1) , ostomsg ( getelt_at_pos p2 ml1 )) ]) ~ (ml2 ++ [ msg ( ostomsg (getelt_at_pos p1 ml2) , ostomsg ( getelt_at_pos p2 ml2 ))]).

(*******************pairing invertible****************************************************************************************)
Axiom FUNCApp_pi1: forall (p :nat)  {m} (ml1 ml2 : mylist m), (ml1 ~ ml2) -> ( [ msg (pi1 (ostomsg (getelt_at_pos p ml1)))] ++ ml1) ~  ( [ msg (pi1 (ostomsg (getelt_at_pos p ml2)))] ++ ml2).
Axiom FUNCApp_pi2: forall (p :nat)  {m} (ml1 ml2 : mylist m), (ml1 ~ ml2) -> ( [ msg (pi2 (ostomsg (getelt_at_pos p ml1)))] ++ ml1 ) ~  ( [ msg (pi2 (ostomsg (getelt_at_pos p ml2)))] ++ ml2).
(*******************************add closed term at pos p***************************************)

Axiom FUNCApp_os : forall (p n :nat) (t: oursum) (ml1 ml2:mylist n),  
                     ml1 ~ ml2 -> (clos_os t = true) -> (@insert_at_pos p t n ml1) ~ (@insert_at_pos p t n ml2).


(*******************RESTR******************************************************)
(******************************************************************************)

(****************** Ind closed under projections ****************)
Axiom RESTR_proj : forall ( p :nat) {m} (ml1 ml2 :mylist m), ml1 ~ ml2 -> (proj_at_pos p ml1) ~ (proj_at_pos p ml2).
(****************** Ind closed under permutations ****************)
Axiom RESTR_swap : forall (p1 p2 : nat) {n} (ml1 ml2 : mylist n), ml1~ ml2 -> (swap_mylist p1 p2 ml1) ~ (swap_mylist p1 p2 ml2).
Axiom RESTR_swapls: forall {n1 n2} (ml1 ml2 : mylist n1) (ml3 ml4 :mylist n2) , (ml1 ++ ml3) ~ (ml2 ++ ml4) -> (ml3 ++ ml1) ~ (ml4 ++ ml2).

Theorem typeeq : forall {m}, (pred (m + 1)) = m.
Proof. intros n. 
assert( (n + 1) = S n). 
apply Nat.add_1_r. rewrite H. 
symmetry . apply pred_Sn.  Qed.


Axiom RESTR_dropls: forall {n} (ml1 ml2: mylist n), ml1 ~ ml2 -> (droplastsec ml1) ~ (droplastsec ml2).
Axiom RESTR_dropone: forall {n} (ml1 ml2: mylist n), ml1 ~ ml2 -> (dropone ml1) ~ (dropone ml2).

(**
Axiom FUNCApp_droplt: forall {n} (ml1 ml2: mylist n), ml1 ~ ml2 -> (droplast3rd ml1) ~ (droplast3rd ml2).

Axiom RESTR_Drop: forall (n :nat)  (ml1 ml2 : mylist n) , ml1 ~ ml2 ->  (dropone ml1) ~ (dropone ml2).
Axiom RESTR1 : forall (n m:nat)  (l1 l1' : mylist n) (l2 l2': mylist m) (x y: oursum), (l1 ++ [x] ++l2) ~ (l1'++ [y]++l2') -> (l1 ++ l2) ~ (l1'++l2').
**)
(********************Ind closed under permutations **********************)
(**

Axiom RESTR_SWAP : forall (p1 p2 : nat) {n} (ml1 ml2 : mylist n), ml1~ ml2 -> (swap_mylist p1 p2 ml1) ~ (swap_mylist p1 p2 ml2).
Axiom RESTR_rev: forall (n:nat) (ml1 ml2: mylist n) , ml1 ~ ml2 -> (reverse ml1) ~ (reverse ml2).*)
Axiom RESTR2 : forall (n1 n2 n3 :nat) (l1 l1' : mylist n1) (l2 l2' : mylist n2) (l3 l3' : mylist n3) (x1 x2 y1 y2 : oursum), (l1 ++ [x1] ++ l2 ++ [x2] ++ l3) ~ (l1' ++ [y1] ++ l2' ++ [y2] ++ l3') ->
 (l1 ++ [x2] ++ l2 ++ [x1] ++ l3) ~ (l1' ++ [y2] ++ l2' ++ [y1] ++ l3').
(********************************************************************************)
Axiom TFDIST: not ([bol TRue]~[bol FAlse]).


(*****Axioms for if_then_else *****************)

(**IFSAME**)


Axiom IFSAME_M: forall (b:Bool) (x : message), (if_then_else_M b x x) # x.
Axiom IFSAME_B: forall (b:Bool) (b1 : Bool),  (if_then_else_B b b1 b1) ## b1.

(**IFEVAL**)

Axiom IFEVAL_B : forall (b1 b2 : Bool)(n:nat),  (if_then_else_B (Bvar n) b1 b2) ## (if_then_else_B (Bvar n) ([n := TRue] b1) ([n := FAlse] b2)).
Axiom IFEVAL_M : forall (t1 t2 : message) (n:nat),  (if_then_else_M (Bvar n) t1 t2) #(if_then_else_M (Bvar n) ((n := TRue) t1) ((n := FAlse) t2)).
Axiom IFEVAL_B' : forall (b b1 b2 : Bool),  (if_then_else_B b b1 b2) ## (if_then_else_B b (subbol_bol' b TRue b1) (subbol_bol' b FAlse b2)).
 
Axiom IFEVAL_M' : forall (b:Bool)(t1 t2  : message),  (if_then_else_M b t1 t2) #(if_then_else_M b (subbol_msg' b TRue t1) (subbol_msg' b FAlse t2)).


(**IFTRue**)

Axiom IFTRUE_M : forall (x y : message),  (if_then_else_M TRue x y) # x .
Axiom IFTRUE_B : forall (b1 b2 : Bool), (if_then_else_B TRue b1 b2) ## b1.


(**IFFAlse**)

Axiom IFFALSE_M: forall (x y : message), (if_then_else_M FAlse x y) # y.
Axiom IFFALSE_B: forall (b1 b2 : Bool),  (if_then_else_B FAlse b1 b2) ## b2.

(********************************************IFBRANCH******************************************)
(**********************************************************************************************)

Axiom IFBRANCH_M: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x x' y y':message), (ml1 ++ [ bol b ; msg x] ) ~  ( ml2 ++ [ bol b'; msg x'])  ->  (ml1 ++ [bol b ; msg y ] ) ~( ml2 ++ [bol b' ; msg y'])
-> (ml1 ++ [bol b ;msg (if_then_else_M b x y)])~ ( ml2 ++ [bol b' ; msg (if_then_else_M b' x' y')]).

Axiom IFBRANCH_B: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(b1 b1' b2 b2':Bool), (ml1 ++ [bol b ;bol b1]) ~ ( ml2 ++ [bol b' ; bol b1'])  ->  (ml1 ++ [ bol b; bol b2]) ~( ml2 ++ [bol b'; bol b2'])
-> (ml1 ++ [ bol b ;bol (if_then_else_B b b1 b2)])~ (  ml2 ++ [bol b' ; bol (if_then_else_B b' b1' b2')] ).




Theorem  IFBRANCH_M1: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x x' y y':message), (ml1 ++ [ bol b ; msg x] ) ~  ( ml2 ++ [ bol b'; msg x'])  ->  (ml1 ++ [bol b ; msg y ] ) ~( ml2 ++ [bol b' ; msg y']) 
                                                                                          -> (ml1 ++  [ msg (if_then_else_M b x y)])~ ( ml2 ++ [ msg (if_then_else_M b' x' y')]).


Proof.  intros. 
apply IFBRANCH_M with (x:= x) (x':=x') (y:= y) (y':= y')  in H. 

apply RESTR_swapls in H.

apply RESTR_dropone in H.  simpl in H. 
apply RESTR_swapls with (ml3:= [msg (if_then_else_M b x y)]) (ml4:= [msg (if_then_else_M b' x' y')]) .  
assumption. assumption. 
Qed.

Theorem ifmor_pair_bvar :  forall (n:nat) (x1 x2 y1 y2 :message), ( if_then_else_M (Bvar n) (x1 , x2) (y1, y2)) # (if_then_else_M (Bvar n) x1 y1, if_then_else_M (Bvar n) x2 y2).
Proof.  intros.
rewrite <- IFSAME_M with (b:= (Bvar n)) (x:= (if_then_else_M (Bvar n) x1 y1, if_then_else_M (Bvar n) x2 y2 )).

rewrite IFEVAL_M with (t1:=  (if_then_else_M (Bvar n) x1 y1, if_then_else_M (Bvar n) x2 y2 )) .  simpl . 

rewrite <- beq_nat_refl.
repeat rewrite IFTRUE_M, IFFALSE_M. 
rewrite IFEVAL_M at 1. simpl. 
reflexivity. 
Qed.

Axiom ifmor_pair_b: forall (b:Bool) (x1 x2 y1 y2 :message), ( if_then_else_M b (x1 , x2) (y1, y2)) # (if_then_else_M b x1 y1, if_then_else_M b x2 y2).

Theorem IFBRANCH_M2: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' y1 y1' y2 y2' :message), (ml1 ++ [ bol b ; msg x1; msg x2] ) ~  ( ml2 ++ [ bol b'; msg x1' ; msg x2'])  ->  (ml1 ++ [bol b ; msg y1 ; msg y2 ] ) ~( ml2 ++ [bol b' ; msg y1'; msg y2']) 
                                                                                     -> (ml1 ++  [ msg (if_then_else_M b x1 y1) ; msg (if_then_else_M b x2 y2) ])~ ( ml2 ++ [ msg (if_then_else_M b' x1' y1') ; msg (if_then_else_M b' x2' y2')]).
Proof. intros. 
apply RESTR_swapls in H  . 
apply RESTR_swapls in H0. 
apply FUNCApp_pair with (p1 :=2) (p2:= 3) in H. 
unfold getelt_at_pos in H.  simpl in H. 
apply FUNCApp_pair with (p1 :=2) (p2:= 3) in H0. 
unfold getelt_at_pos in H0; simpl in H0.  
(************H************************)
apply RESTR2 with (l1:=[])(x1:= bol b) (l2:= []) (l3:= [msg x2]++ ml1 ++ [msg ( x1, x2 )]) (l1':= []) (l2':=[])  (l3':= [msg x2']++ ml2 ++ [msg ( x1', x2' )])  (x2:= msg x1) (y1 := bol b') (y2:= msg x1') in H.
simpl in H.  
apply RESTR_dropone in H.  
unfold dropone in H; simpl in H.

apply RESTR2 with (l1:=[bol b])(x1:= msg x2) (x2:= msg (x1 , x2)) (l2:=ml1) (l3:= []) (l1':= [bol b']) (l2':= ml2)  (l3':= [])  (y1 := msg x2') (y2:= msg (x1',x2')) in H.

simpl in H. 
assert( ( ([bol b ; msg (x1, x2 ) ] ++ ml1) ++ [msg x2]) ~ ( ([bol b' ; msg (x1', x2')] ++ ml2) ++ [msg x2'])).
assumption.  clear H. 
apply RESTR_swapls in H1. 
apply RESTR_dropone in H1.  
unfold dropone in H1; simpl in H1.
assert ( ([bol b ; msg (x1, x2)] ++ ml1) ~  ( [ bol b' ; msg (x1' , x2')] ++ ml2)).
assumption. clear H1. 
apply RESTR_swapls in H. 
(***********************H0*******************)

apply RESTR2 with (l1:=[])(x1:= bol b) (l2:= []) (l3:= [msg y2]++ ml1 ++ [msg ( y1, y2 )]) (l1':= []) (l2':=[])  (l3':= [msg y2']++ ml2 ++ [msg ( y1', y2' )])  (x2:= msg y1) (y1 := bol b') (y2:= msg y1') in H0.
simpl in H0.  
apply RESTR_dropone in H0.  
unfold dropone in H0; simpl in H0.

apply RESTR2 with (l1:=[bol b])(x1:= msg y2) (x2:= msg (y1 , y2)) (l2:=ml1) (l3:= []) (l1':= [bol b']) (l2':= ml2)  (l3':= [])  (y1 := msg y2') (y2:= msg (y1',y2')) in H0.

simpl in H0.
assert( (([bol b ; msg (y1, y2 ) ] ++ ml1) ++ [msg y2]) ~ (( [bol b' ; msg (y1', y2')] ++ ml2) ++ [msg y2'])).
assumption.  clear H0. 
apply RESTR_swapls in H1. 
apply RESTR_dropone in H1. 
unfold dropone in H1; simpl in H1.

assert ( ([bol b ; msg (y1, y2)] ++ ml1) ~  ( [ bol b' ; msg (y1' , y2')] ++ ml2)).
assumption. clear H1. 
apply RESTR_swapls in H0. 
(****************************************************************)
apply IFBRANCH_M with (x:= (x1, x2)) (x' := (x1', x2') ) (y := (y1, y2)) (y':= (y1', y2')) in H. 
Focus 2. assumption.
 
repeat rewrite ifmor_pair_b in H. 
apply RESTR_swapls in H. 
apply RESTR_dropone in H.  simpl in H. 

apply FUNCApp_pi2 with (p:=1) in H. simpl in H. 
repeat rewrite proj2 in H. 

 

apply FUNCApp_pi1 with (p:=2) in H. simpl in H. 
repeat rewrite proj1 in H. simpl in H. 
  
assert( [msg (if_then_else_M b x1 y1) ; msg (if_then_else_M b x2 y2)] ++ [ msg ((if_then_else_M b x1 y1 ),  (if_then_else_M b x2 y2 ))] ++ ml1) ~
      ( [msg (if_then_else_M b' x1' y1') ; msg (if_then_else_M b' x2' y2')] ++[ msg ( if_then_else_M b' x1' y1', if_then_else_M b' x2' y2')] ++ ml2).
assumption.              
apply RESTR_swapls in H1.
apply RESTR_dropone in H1.
unfold dropone in H1; simpl in H1.
clear H. 
assumption.

Qed.

(***********similarly the following can be proved ***************************************************************************************************************)
(****************************************************************************************************************************************************************)

Axiom IFBRANCH_M3: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' y1 y1' y2 y2' y3 y3' :message), (ml1 ++ [ bol b ; msg x1; msg x2 ; msg x3] ) ~  ( ml2 ++ [ bol b'; msg x1' ; msg x2' ; msg x3'])  ->  (ml1 ++ [bol b ; msg y1 ; msg y2 ; msg y3 ] ) ~( ml2 ++ [bol b' ; msg y1'; msg y2' ; msg y3']) 
                                                                                                                           -> (ml1 ++  [ msg (if_then_else_M b x1 y1) ; msg (if_then_else_M b x2 y2) ; msg (if_then_else_M b x3 y3) ])~ ( ml2 ++ [ msg (if_then_else_M b' x1' y1') ; msg (if_then_else_M b' x2' y2') ; msg (if_then_else_M b' x3' y3')]).



Axiom IFBRANCH_M4: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' x4 x4' y1 y1' y2 y2' y3 y3' y4 y4' :message), (ml1 ++ [ bol b ; msg x1; msg x2 ; msg x3; msg x4] ) ~  ( ml2 ++ [ bol b'; msg x1' ; msg x2' ; msg x3'; msg x4'])  ->  (ml1 ++ [bol b ; msg y1 ; msg y2 ; msg y3; msg y4 ] ) ~( ml2 ++ [bol b' ; msg y1'; msg y2' ; msg y3'; msg y4'])  -> (ml1 ++  [ msg (if_then_else_M b x1 y1) ; msg (if_then_else_M b x2 y2) ; msg (if_then_else_M b x3 y3) ; msg (if_then_else_M b x4 y4) ])~ ( ml2 ++ [ msg (if_then_else_M b' x1' y1') ; msg (if_then_else_M b' x2' y2') ; msg (if_then_else_M b' x3' y3') ;  msg (if_then_else_M b' x4' y4')]).


Axiom IFBRANCH_M5: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' y1 y1' y2 y2' y3 y3' y4 y4' y5 y5' :message), (ml1 ++ [ bol b ; msg x1; msg x2 ; msg x3; msg x4 ; msg x5] ) ~  ( ml2 ++ [ bol b'; msg x1' ; msg x2' ; msg x3'; msg x4'; msg x5'])  ->  (ml1 ++ [bol b ; msg y1 ; msg y2 ; msg y3; msg y4; msg y5 ] ) ~( ml2 ++ [bol b' ; msg y1'; msg y2' ; msg y3'; msg y4'; msg y5'])  -> (ml1 ++  [ msg (if_then_else_M b x1 y1) ; msg (if_then_else_M b x2 y2) ; msg (if_then_else_M b x3 y3) ; msg (if_then_else_M b x4 y4); msg (if_then_else_M b x5 y5) ])~ ( ml2 ++ [ msg (if_then_else_M b' x1' y1') ; msg (if_then_else_M b' x2' y2') ; msg (if_then_else_M b' x3' y3') ;  msg (if_then_else_M b' x4' y4'); msg (if_then_else_M b' x5' y5')]).

Axiom IFBRANCH_M7: forall (n: nat) (ml1 ml2 : mylist n) (b b' : Bool)(x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' x6 x6' x7 x7' y1 y1' y2 y2' y3 y3' y4 y4' y5 y5' y6 y6' y7 y7' :message), (ml1 ++ [ bol b ; msg x1; msg x2 ; msg x3; msg x4 ; msg x5; msg x6 ; msg x7] ) ~  ( ml2 ++ [ bol b'; msg x1' ; msg x2' ; msg x3'; msg x4'; msg x5' ; msg x6' ; msg x7'])  ->  (ml1 ++ [bol b ; msg y1 ; msg y2 ; msg y3; msg y4; msg y5; msg y6 ; msg y7 ] ) ~( ml2 ++ [bol b' ; msg y1'; msg y2' ; msg y3'; msg y4'; msg y5'; msg y6' ; msg y7'])  -> (ml1 ++  [ msg (if_then_else_M b x1 y1) ; msg (if_then_else_M b x2 y2) ; msg (if_then_else_M b x3 y3) ; msg (if_then_else_M b x4 y4); msg (if_then_else_M b x5 y5); msg (if_then_else_M b x6 y6); msg (if_then_else_M b x7 y7) ])~ ( ml2 ++ [ msg (if_then_else_M b' x1' y1') ; msg (if_then_else_M b' x2' y2') ; msg (if_then_else_M b' x3' y3') ;  msg (if_then_else_M b' x4' y4'); msg (if_then_else_M b' x5' y5'); msg (if_then_else_M b' x6' y6'); msg (if_then_else_M b' x7' y7')]).

Fixpoint nestpair {n} (ml:mylist n ) : message:=

        match ml with
        | [] => O
         | h :: [] => ostomsg h
         | h :: t => ( ostomsg h, nestpair t)
       end.

(**
Fixpoint fold {n} (b:Bool) (l1 l2 : mylist n): list message :=
match n, l1, l2 with
|0, [] , [] => nil
|1, h1::[], h2::[] => (cons (if_then_else_M b (ostomsg h1) (ostomsg h2)) nil)
|S n', (Cons  _ h1  t1), (Cons _ h2 t2) =>( app (cons  (if_then_else_M b (ostomsg h1) (ostomsg h2)) nil) (fold b t1 t2 ) )
| _, _ , _ => nil
end.
**)

Axiom IFBRANCH_Mn: forall (n1 n2 :nat) (ml1 ml2 : mylist n1) (ml3 ml4 ml5 ml6 : mylist n2) (b b': Bool) ,   (ml1 ++ [bol b] ++ ml3 ) ~ (ml2 ++ [bol b'] ++ ml4) -> (ml1 ++ [bol b] ++ ml5) ~ (ml2 ++ [bol b'] ++ ml6) -> (ml1 ++ [msg (if_then_else_M b (nestpair ml3) (nestpair ml4))]) ~ (ml2 ++ [ msg (if_then_else_M b' (nestpair ml5) (nestpair ml6))]).




(*******************************Axioms for Fresh names*****************************************)
(**********************************************************************************************)

Axiom FRESHNEQ: forall (n : nat) (m : message), ((clos_msg m) = true)/\ ( (Fresh [n] [msg m]) = true) ->[bol (EQ_M (N n) m)]~ [bol FAlse] .

Axiom FRESHIND: forall (n n1 n2:nat) (v w: mylist n), ((clos_mylist (v++w)) = true) /\ ( (Fresh [ n1] (v++w)) = true) /\ ( (Fresh [ n2] (v++w)) = true) /\  (v ~ w) <-> ((msg (r n1) ) +++ v) ~ (( msg (r n2)) +++w ) .
Axiom FRESHIND_rs : forall (n n1 n2:nat) (v w: mylist n), ((clos_mylist (v++w)) = true) /\ ( (Fresh [ n1] (v++w)) = true) /\ ( (Fresh [ n2] (v++w)) = true) /\  (v ~ w) <-> ((msg  (N n1)) +++ v) ~ (( msg  (N n2)) +++w ) .


(*****************************************************************************************************************************************************************)
(****Fresh [n;n1;n2;n3]-> [G(n); g(n);g(n)^(r (n1));g(n)^(r (n2)); g(n)^(r (n1))(r (n2))] ~[G(n); g(n);g(n)^(r (n1));g(n)^(r (n2)); g(n)^(r (n3))]*****************)

Axiom DDH : forall (n n1 n2 n3: nat),  (Fresh [ n ; n1 ;  n2  ; n3 ] []) = true-> 
[ msg (G n) ; msg (g n) ; msg (exp (G n) (g n) (r  n1)) ; msg (exp (G n) (g n) (r  n2)) ; msg (exp (G n) (exp (G n) (g n) (r  n1)) (r  n2))]
~ [msg (G n) ; msg (g n) ; msg (exp (G n) (g n) (r  n1)) ; msg (exp (G n) (g n) (r n2)) ; msg (exp (G n) (g n) (r n3))]  .

Goal (f [ (if_then_else_M TRue O O)]) # (f [ O]).
rewrite IFTRUE_M. reflexivity.  Qed. 
 Check f.
End Core_Axioms.


Eval compute in sublist 0 3 [ msg O; msg  (N 1); msg (N 2)].
Check f.

