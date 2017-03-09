
Load "CORE_AXIOMS".
(*************************Auxilary Axioms*********************************)
(****************************************************************************)


(*****Equality closed under substitution******)

Axiom Forall_ELM_EVAL_M: forall (x:Bool) (n:nat) (t1 t2 :message), ( t1 # t2 ) ->  ((( n:=x )t1) # ((n:=x)t2)).
Axiom Forall_ELM_EVAL_B: forall (b:Bool) (n:nat) (b1 b2 :Bool), (  b1 ## b2 ) ->  ( ([n:=b] b1) ## ([n:=b] b2)).

Axiom Forall_ELM_EVAL_M1: forall (x:message) (n:nat) (t1 t2 :message), (t1 # t2 ) ->  ({{n:=x}} t1 # {{n:=x}}t2).
Axiom Forall_ELM_EVAL_B1: forall (b:message) (n:nat) (b1 b2 :Bool), ( b1 ## b2 ) ->  ( [[n:=b]] b1 ## [[n:=b]] b2).

Axiom Forall_ELM_EVAL_M2: forall (x:Bool) (n:nat) (t1 t2 :message), (t1 # t2)  ->  ( (( n:=x )t1) # ((n:=x)t2 )).
Axiom Forall_ELM_EVAL_B2: forall (b:Bool) (n:nat) (b1 b2 :Bool), (b1 ## b2)  ->   ( [n:=b] b1 ## [n:=b] b2).

Axiom Forall_ELM_EVAL_M3: forall (x:message) (n:nat) (t1 t2 :message),  ( t1 # t2)  ->  ( {{n:=x}} t1  # {{n:=x}}t2).
Axiom Forall_ELM_EVAL_B3: forall (b:message) (n:nat) (b1 b2 :Bool), ( b1 ## b2) ->   ( [[n:=b]] b1 ## [[n:=b]] b2).





(***substitutions under attacker functions**********)
(**
Axiom sub_msg_f : forall ( n :nat) (s:message) {m} (l: ilist message m), {{ n := s }} (f l) # (f (submsg_mlist n s l)).
Axiom sub_bol_f : forall ( n :nat) (b: Bool) {m} (l: ilist message m), ( n := b ) (f l) # (f (subbol_mlist n b l)).
**)

(**********************************There exists a natural number which doesn't occur in lists of terms*********************************)
Axiom existsn_mylist: forall (m1 m2 :nat) (nl : ilist nat m1)(bl:mylist m2), exists n , (notoccur_nlist n nl = true) /\ (notoccur_mylist n bl = true).
Axiom existsn_Blist : forall (m1 m2 :nat) (nl : ilist nat m1)(bl:ilist Bool m2), exists n , (notoccur_nlist n nl = true) /\ (notoccur_blist n bl = true).
Axiom existsn_Mlist: forall (m1 m2 :nat) (nl : ilist nat m1)(ml:ilist message m2), exists n , (notoccur_nlist n nl = true) /\ (notoccur_mlist n ml = true).
(***
Axiom subconct: forall (n1 n2 n:nat) (ml1 : mylist n1)(ml2 : mylist n2)(b:Bool), ((subbol_mylist n b (ml1 ++ ml2)) =(subbol_mylist n b ml1 ++ subbol_mylist n b ml2)).


Axiom subinmsg : forall (n : nat)(b:Bool) (t1:message), ( (subbol_os n b (msg t1) ) = (msg ((n := b) t1))).
Axiom subinbol : forall (n : nat)(b:Bool) (t1:Bool), ( (subbol_os n b (bol t1) ) = (bol ([n := b] t1))).
**)
(****************************some axioms***************************)

Axiom notocc_bolmm: forall (n1 n2 : nat) (b: Bool) (m1 m2 : message), (notoccur_msg n1 m2) = true -> ( n1 :=  b)  ((submsg_msg n2 m1)  m2) = (submsg_msg n2 (( n1 := b) m1)) m2 .

(*Axiom occ_bolmm: forall (n1 n2 : nat) (b: Bool) (m1 m2 : message), (notoccur_msg n1 m2) = false -> ( n1 :=  b)  ((submsg_msg n2 m1)  m2) = (submsg_msg n2 (( n1 := b) m1)) (( n1 := b)m2) .*)

Axiom notocc_bolbb : forall  (n1 n2 :nat) (b b1 b2:Bool), (notoccur_bol n1 b2) = true -> ([ n1 :=  b]  [ n2 := b1]  b2)  =    ( [ n2 := ([n1:=b] b1)]  b2) .


(*Axiom occ_bolbb : forall  (n1 n2 :nat) (b b1 b2:Bool), (notoccur_bol n1 b2) = false -> ([ n1 :=  b]  [ n2 := b1]  b2)  =    ( [ n2 := ([n1:=b] b1)]  ([n1:=b] b2)) .*)

Axiom notocc_bolmb : forall (n1 n2 :nat) (b  b1:Bool) (m:message),(notoccur_bol n1 b1) = true -> ([ n1 :=  b]  [[ n2 := m]]  b1)  =    ( [[ n2 := ((n1 := b) m)]]  b1).

(*Axiom occ_bolmb : forall (n1 n2 :nat) (b  b1:Bool) (m:message),(notoccur_bol n1 b1) = false -> ([ n1 :=  b]  [[ n2 := m]]  b1)  =    ( [[ n2 := ((n1 := b) m)]]  ([ n1 :=  b] b1)).*)

Axiom notocc_bolbm : forall (n1 n2 :nat) (b  b1:Bool) (m:message),(notoccur_msg n1 m) = true -> ( ( n1 :=  b)  (( n2 := b1) m)  =    ( ( n2 := ([n1 := b] b1))  m)).

(*Axiom occ_bolbm : forall (n1 n2 :nat) (b  b1:Bool) (m:message),(notoccur_msg n1 m) = false -> ( ( n1 :=  b)  (( n2 := b1) m)  =    ( ( n2 := ([n1 := b] b1))  (n1 := b)m)).*)



(********************************************************************************)

Axiom notoccn_Bool: forall (n:nat)(b t:Bool), ((notoccur_bol n t) = true )-> ([n := b]t =  t).
Axiom notoccn_msg: forall (n:nat)(b:Bool)(t:message), ((notoccur_msg n t) = true) -> ((n:= b)t) = t.


(***********************************************************************************)
Axiom  invarsub_Bmsg : forall(n:nat)(t:message), ((n:= (Bvar n))t = t).
Axiom invarsub_BBool: forall(n:nat)(b:Bool), ([n:=(Bvar n)] b) = b.
Axiom invarsub_mBool : forall(n:nat)(b: Bool), ([[n:= (Mvar n)]] b) = b. 
Axiom invarsub_mmsg : forall(n:nat)(t: message),{{n:= (Mvar n)}} t = t. 



(**Axiom RESTR_Perm: forall(n1 n2 n3 n4 n5:nat) (nl1 ml1 : mylist n1)(nl2 ml2 : mylist n2)(nl3 ml3 : mylist n3)(ml4 nl4 : mylist n4) (ml5 nl5 : mylist n5), (nl1++nl2++nl3++nl4++nl5)~(ml1++ml2++ml3++ml4++ml5)  -> (nl1 ++nl4++nl2++nl5++nl3)~ (ml1 ++ml4++ml2++ml5++ml3).**)

(*********************Axiliary axioms****************************)

(***Axiom simpinsub_B : forall (n n1 n2 n3 n4 n5 n6 :nat)(t1 t2 : Bool), (if_then_else_B (Bvar n) [n5 := if_then_else_B TRue (Bvar n1) (Bvar n2)](t1)
   [n6 := if_then_else_B FAlse (Bvar n3) (Bvar n4)](t2))## (if_then_else_B (Bvar n) [n5 := Bvar n1](t1) [n6 := Bvar n4](t2)).**)


