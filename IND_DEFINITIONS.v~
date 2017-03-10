
(***************IND-Definitions**************************************************)
(********************************************************************************)
 (*Extraction Language Ocaml.*)
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Plus.
Require Import Coq.Lists.List .
Require Import Le Gt Minus Bool Setoid.
Require Import List.
Require Import Coq.Lists.ListSet .
Require Import Coq.Init.Peano.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Init.Logic.
Require Import Coq.NArith.BinNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.SetoidTactics.
Require Import Relation_Definitions.
Require Import Morphisms.
Require Import Setoid.
Require Import Program.
Require Import Coq.Logic.JMeq.
Eval compute in (pair 1 2). 

(*The types message and bool are defined as inductive types**)

Inductive message : Type :=
| Mvar : nat -> message
| O: message
| acc : message
| lsk : message
| lnc : message
| N: nat -> message
| if_then_else_M: Bool -> message -> message -> message
| exp : message -> message -> message -> message
| pair: message -> message -> message
| pi1 : message -> message
| pi2 : message -> message
| ggen : message -> message 
| rr : message -> message
| new : message
| act : message -> message
| m : message -> message
| nc : message -> message
| enc: message -> message -> message->message
| dec : message-> message -> message
| to : message -> message
| k: message -> message
| sign : message -> message -> message
| reveal: message -> message
| i : nat -> message
| L : message -> message   
| rs : message -> message            
| f: list message  -> message
with Bool : Type :=
| Bvar: nat -> Bool 
| TRue: Bool
| FAlse: Bool
| EQ_B : Bool -> Bool -> Bool
| EQ_M : message -> message -> Bool
| if_then_else_B :  Bool -> Bool -> Bool -> Bool
| EQL : message -> message -> Bool
| ver : message -> message -> message -> Bool.

(***polymorphic length-indexed list defined*****)

Inductive ilist (A:Type) : nat -> Type :=
| Nil : ilist A 0
| Cons: forall n, A-> ilist A n  -> ilist A (S n).

(*Notations *)

Notation "x :: l" := (Cons _ _ x l )(at level 60, right associativity).
Notation "[]" := (Nil _) (at level 1).
Check Nil.
Notation "[ x ; .. ; y ]" := (Cons _ _ x ..(Cons _ _ y (Nil _)) ..) .

Check Nil.

(*oursum is a type inductively defined in message and bool types*)

Inductive oursum : Type:= 
| msg :  message -> oursum
| bol :  Bool  -> oursum.

(*length-indexed list of type oursum that takes length as an argument*)
(*it also called as mylist *)
Definition mylist : nat-> Type := ilist oursum.

(*definition of notb in our language*)

Definition  notb (b: Bool) := (if_then_else_B b (FAlse) (TRue)).
Check notb.

(* if_then is defined*)
Definition if_then (b:Bool) (t:message) := if_then_else_M b t O.
(* andB is defined usign the if_then_else_B symbol*)
Definition andB (b1 b2 :Bool) := if_then_else_B b1 b2 FAlse.
(* andB is represented with symbol & *)
Notation " b1 & b2" := (andB b1 b2 ) (at level 0).

(**pairing notations*)
Notation "( x , y )" := (pair x y) (at level 0).
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) (at level 0).
(*ggen is randomized algorithm takes name and outputs a pair group descriptor and generator*)
(*Group descriptor G--proj1 of the pair *)
Definition G (n: nat) := (pi1 (ggen (N n))).
(*Group generator g-- proj2 of the pair*)
Definition g( n:nat) := (pi2 (ggen (N n))).
(*k acts as key generation algorithm that take agent name and output a public and private key pair*)
Definition pk (a:message) := (pi1 (k a)).
Definition sk (a:message) := (pi2 (k a)).
(*rr represents randomness*)
Definition r (n:nat) := (rr (N n)).

(*check if a term of oursum starts with bol*)
Definition chkbol_os (a : oursum) : bool  :=
match a with
| bol a' => true
| msg a' => false
end.

(*check if a term of oursum starts with msg*)

Definition chkmsg_os (a : oursum) : bool  :=
match a with
| bol a' => false
| msg a' => true
end.

(*get bool term out of a term of type oursum*)

Definition ostobol (a :oursum) : Bool :=
 match a with
| bol a' => a'
| msg a' => TRue
end. 
(*get msg term out of a term of type oursum*)
          
Definition ostomsg (a : oursum) : message :=
match a with
| bol a' => O
| msg a' => a'
end.


(*converting ilist message n to mylist n*)

Fixpoint conv_mlist_mylist {n:nat} (ml : ilist message n) : mylist n :=

match ml with
| Nil => []
| a :: h => msg a :: (conv_mlist_mylist h)
end.

(*converting list of bool to mylist n*)


Fixpoint conv_blist_mylist {n:nat} (ml : ilist Bool n) : mylist n :=

match ml with
| Nil => []
| a :: h => bol a :: (conv_blist_mylist h)
end.

(*converting list of messages to mylist n*)

Fixpoint conv_listm_mylist ( l :  list message) : mylist (length l) :=

match l with
| nil => []
| cons a h => msg a :: (conv_listm_mylist h)
end.



(*mylist n to type list message*)

Fixpoint conv_mylist_listm {n:nat} (osl: mylist n) : list message :=

match osl with
| [] => nil
| a :: h => cons  (if (chkmsg_os a) then (ostomsg a) else O) (conv_mylist_listm h)
 
end.
(*mylist n to list oursum*)

Fixpoint conv_mylist_listos {n:nat} (osl:mylist n) :list oursum :=
match osl with 
| [] => nil
| a :: h => (cons a (conv_mylist_listos h ) )
end.

(*mylist n to ilist Bool n*)

Fixpoint conv_mylist_listb {n:nat} (osl: mylist n) : ilist Bool n :=

match osl with
| [] => @Nil Bool
| a :: h => Cons _ _ (if (chkbol_os a) then (ostobol a) else TRue) (conv_mylist_listb h)
 
end.

(*list oursum to mylist (length l)*)


Fixpoint conv_listos_mylist (l : list oursum) : (mylist (length l)) :=
match l with
| nil => []
| cons h t => h:: (conv_listos_mylist t)
end.

(*sublist of list of type A***)

Definition sublist {A:Type} (n m:nat) (l:list A) :=
  skipn n (firstn m l).

 
 
(*substitution: x<-- s in t, where x, s, and t are bool or message*)

Reserved Notation "'[[' x ':=' s ']]' t" (at level 0).
Reserved Notation "'{{' x ':=' s '}}' t" (at level 0).
Fixpoint submsg_bol (n : nat )(s:message) (t:Bool) : Bool :=
 match t with 
| Bvar n' =>  Bvar n'
| FAlse => FAlse
| TRue => TRue
| EQ_B  b1 b2 =>  EQ_B  ([[n:= s]]b1) ([[n:= s]] b2)
| EQ_M t1 t2 => EQ_M ( {{n:= s }} t1) ( {{ n:=s }} t2)
| if_then_else_B t1 t2 t3 => if_then_else_B  ([[n:=s]]t1) ( [[n:=s]] t2) ( [[n:=s]]t3) 
| EQL t1 t2 => EQL ( {{ n := s }} t1) ( {{ n:=s }} t2)
| ver t1 t2 t3 => ver ({{n:=s}}t1) ({{n:=s}}t2) ({{n:=s}}t3)

 end
where "'[[' x ':=' s ']]' t" := (submsg_bol x s t)
with submsg_msg (n : nat )(s:message) (t:message) : message :=
 match t with 
| if_then_else_M b3 t1 t2 => if_then_else_M ([[n:=s]] b3) ({{n:=s}} t1) ({{n:=s}} t2)
| (Mvar n') =>  if (beq_nat n' n) then s else t
| O => O
| lnc => lnc
| lsk => lsk
| acc => acc
| N n'=> N n'
| new => new
| exp t1 t2 t3 => exp ( {{ n :=s }} t1) ( {{ n:=s }} t2) ( {{ n:=s }} t3)
| pair t1 t2 => pair ( {{ n:=s }} t1) ( {{ n:=s }} t2)
| pi1 t1 => pi1 ( {{ n:=s }} t1) 
| pi2 t1 => pi2 ( {{ n:=s }} t1) 
| ggen t1 => ggen ( {{ n:=s }} t1)
| act t1 => act( {{ n:=s }} t1)
| rr t1 => rr ({{ n:=s}}t1)
| rs t1 => rs ({{n:=s}} t1)
| L t1 => L ({{ n:=s}}t1)
| m t1 => m ( {{ n:=s }} t1)
| enc t1 t2 t3 =>  enc ( {{ n :=s }} t1) ( {{ n:=s }} t2) ( {{ n:=s }} t3)
| dec t1 t2 => dec ( {{ n:=s }} t1) ( {{ n:=s }} t2)
| k t1 => k ( {{ n:=s }} t1) 
| nc t => nc  ( {{ n:=s }} t) 
| to t1 => to  ( {{ n:=s }} t1) 
| reveal t1 => reveal  ( {{ n:=s }} t1)
| sign t1 t2 => sign ({{n:=s}}t1) ({{n:=s}}t2)
| i n' => i n' 
| f l =>  (f (@map message message  (submsg_msg n s) l))
 end

where "'{{' x ':=' s '}}' t" := (submsg_msg x s t).


(*substitution: x <- s in t, x is of type variable, t is of oursum*)

Definition submsg_os (n:nat)(s:message) (t:oursum):oursum :=
match t with 
| msg t1 =>  msg ({{n := s}} t1)
| bol b1 =>  bol ( [[n := s]] b1)
end.

(*substitution in ilist message n' *)
Fixpoint submsg_mlist  {n' :nat} (n:nat)(s:message)(l : ilist message n') : ilist message n' :=
match l with 
| [] => []
| h::t  =>  ({{n := s}} h) :: (submsg_mlist n s t )
end.
Eval compute in (submsg_msg 1 O  (f [ (Mvar 1) ; (N 2) ; (N 1)])).

Eval compute in  ( {{ 1 := O }} (N 1) ).


(****substitutions for Bool var in Bool and message*)

Reserved Notation "'[' x ':=' s ']' t" (at level 0).
Reserved Notation "'(' x ':=' s ')' t" (at level 0).
Fixpoint subbol_bol (n : nat )(s:Bool) (t:Bool) : Bool :=
 match t with 
| Bvar n' =>  if (beq_nat n' n) then s else t
| FAlse => FAlse
| TRue => TRue
| EQ_B  b1 b2 =>  EQ_B  ([n:=s] b1) ([n:=s] b2)
| EQ_M t1 t2 => EQ_M ((n:= s)t1) ((n:=s) t2)
| if_then_else_B t1 t2 t3 => if_then_else_B  ([n:=s] t1) ([n:=s] t2) ([n:=s] t3) | EQL t1 t2 => EQL ((n:=s) t1) ((n:=s) t2)
| ver t1 t2 t3 => ver ((n:=s)t1) ((n:=s)t2) ((n:=s)t3)

 end
where "'[' x ':=' s ']' t" := (subbol_bol x s t)
with subbol_msg (n : nat )(s:Bool) (t:message) : message :=
 match t with 
| if_then_else_M b3 t1 t2 => if_then_else_M ([n:=s] b3) ((n:=s)t1) ( (n:=s)t2)
| (Mvar n') => (Mvar n')
| acc => acc
| O => O
| lnc => lnc
| lsk => lsk
| N n'=> N n'
| new => new
| exp t1 t2 t3 => exp (( n:=s ) t1) (( n:=s) t2) (( n:=s ) t3)
| pair t1 t2 => pair (( n:=s ) t1) (( n:=s) t2)
| pi1 t1 => pi1 (( n:=s ) t1) 
| pi2 t1 => pi2 (( n:=s ) t1) 
| ggen t1 => ggen (( n:=s ) t1)
| act t1 => act(( n:=s ) t1)
|rr t1 => rr ((n:=s) t1)
|rs t1 => rs ((n:=s) t1)
| L t1 => L ((n:=s) t1)
| m t1 => m (( n:=s ) t1)
|enc t1 t2 t3 => enc (( n:=s ) t1) (( n:=s) t2) (( n:=s ) t3)
|dec t1 t2 => dec  (( n:=s ) t1) (( n:=s) t2) 
|k t1 => k (( n:=s ) t1)
| nc t1 =>  nc (( n:=s ) t1)
| to t1 => to (( n:=s ) t1)
| reveal t1 => reveal (( n:=s ) t1)
| sign t1 t2 => sign ((n:=s)t1) ((n:=s)t2)
| i n' => i n'
|  f l => (f (@map message message (subbol_msg n s) l))

 end
where "'(' x ':=' s ')' t" := (subbol_msg x s t).




(*substitution for Bool var in a term of type oursum*)

Definition  subbol_os (n:nat)(s:Bool) (t:oursum):oursum :=
match t with 
|msg t1 =>  msg ((n := s) t1)
|bol b1 =>  bol ( [n := s] b1)
end.
(*
Fixpoint subbol_mlist (n:nat) (b:Bool) {m} (l:ilist message m) : ilist message m :=
match l with 
| [] => []
| h::tl => ((n:=b) h) :: (subbol_mlist n b tl)
end.
*)
(*testing properties on list elements***)
 Fixpoint test_list {X:Type} (test: X -> bool) (l:list X)
                : bool := 
match l with
| nil => true
| cons h t => if (test h) then (test_list test t) else false
end.
  

Check existsb.


(**check if a term is ground****)
 Fixpoint clos_bol (b :Bool):bool:=
 match b with 
| Bvar n' =>  false
| FAlse => true
| TRue => true
| EQ_B  b1 b2 =>  (andb (clos_bol b1) (clos_bol b2))
| EQ_M t1 t2 => (andb (clos_msg t1) (clos_msg t2))
| if_then_else_B b t1 t2 =>  andb (clos_bol b) (andb (clos_bol t1) (clos_bol t2))
| EQL t1 t2 => (andb (clos_msg t1) (clos_msg t2))
| ver t1 t2 t3 => (andb (andb (clos_msg t1) (clos_msg t2)) (clos_msg t3))
end
with clos_msg (t:message) : bool:=
match t with 
| if_then_else_M b t1 t2 => andb (clos_bol b) (andb (clos_msg t1) (clos_msg t2))
| (Mvar n') => false
| acc => true
| O => true
| lsk => true
| lnc => true
| N n'=> true
| new => true
| exp t1 t2 t3 => andb (clos_msg t1) (andb (clos_msg t2) (clos_msg t3))
| pair t1 t2 => (andb (clos_msg t1) (clos_msg t2))
| pi1 t1 => (clos_msg t1) 
| pi2 t1 => (clos_msg t1) 
| ggen t1 => (clos_msg t1) 
| act t1 => (clos_msg t1) 
| rr t1 => (clos_msg t1)
| rs t1 => (clos_msg t1)
| L t1 => (clos_msg t1)           
| m t1 =>  (clos_msg t1) 
| enc t1 t2 t3 => andb (clos_msg t1) (andb (clos_msg t2) (clos_msg t3))
| dec t1 t2 =>(andb (clos_msg t1) (clos_msg t2))
| k t1 => (clos_msg t1) 
| nc t1 => (clos_msg t1) 
| to t1 => (clos_msg t1)
| reveal t1 => (clos_msg t1)
| sign t1 t2 => (andb (clos_msg t1) (clos_msg t2))
| i n => true
| f  l => (@forallb message clos_msg l)
end.

Eval compute in (clos_msg  (f [(if_then_else_M (Bvar 1) O O)])).

(*check if a term of type of oursum is closed***)
Definition clos_os (t:oursum): bool :=
match t with 
| msg t1 =>  clos_msg (t1)
| bol b1 =>  clos_bol (b1)
end. 


(*check if every element of message list is closed***)

Fixpoint clos_listm (l: list message):bool:=
match l with 
| nil=> true
| cons  h t => (andb (clos_msg h) (clos_listm t))
end.

Eval compute in clos_listm [O ; O].

(*check if every element of Bool list is closed**)

Fixpoint clos_listb (l: list Bool ):bool:=
match l with 
| nil=> true
| cons h t => (andb (clos_bol h) (clos_listb t))
end.

Eval compute in (clos_listb [FAlse; (Bvar 1)]).

(**check if mylist is closed***)

Fixpoint clos_mylist {n:nat} (l: mylist n):bool :=
match l with 
| Nil => true
| h :: t => (andb (clos_os h) (clos_mylist t))
 end.

(**check if a variable occure in a term of type message or Bool*)

Fixpoint var_free_bol (n : nat )(t:Bool) : bool :=
 match t with 
| Bvar n' => if (beq_nat n' n) then true else false
| FAlse => false
| TRue => false
| EQ_B  b1 b2 =>  orb (var_free_bol n b1)  ( var_free_bol n b2)
| EQ_M t1 t2 => orb (var_free_msg n t1) ( var_free_msg n t2)
| if_then_else_B t1 t2 t3 => orb ( var_free_bol n t1)  (orb (var_free_bol n t2)(var_free_bol n t3) )
| EQL t1 t2 => orb ( var_free_msg n t1) ( var_free_msg n t2)
| ver t1 t2 t3 => (orb  (orb (var_free_msg n t1) (var_free_msg n t2)) (var_free_msg n t3))

 end
with var_free_msg (n : nat )(t:message) : bool :=
 match t with 
| if_then_else_M b3 t1 t2 => orb (var_free_bol n b3) (orb ( var_free_msg n  t1)( var_free_msg n t2))
| (Mvar n') => if (beq_nat n' n) then true else false
| O => true
| acc => true
| lnc => true
| lsk => true
| N n'=> true
| new => true
| exp t1 t2 t3 => orb ( var_free_msg n t1) (orb ( var_free_msg n t2) ( var_free_msg n t3))
| pair t1 t2 => orb(var_free_msg n t1) ( var_free_msg n t2)
| pi1 t1 => ( var_free_msg n t1)
| pi2 t1 => (var_free_msg n t1)
| ggen t1 => (var_free_msg n t1)
| act t1 => ( var_free_msg n t1)
| rr t1 => (var_free_msg n t1)
| rs t1 => (var_free_msg n t1)
| L t1 => (var_free_msg n t1)
| m t1 => ( var_free_msg n t1)
| enc t1 t2 t3 =>  orb (var_free_msg n t1) (orb ( var_free_msg n t2) ( var_free_msg n t3))
| dec t1 t2 => orb( var_free_msg n t1) (var_free_msg n t2)
| k t1 => (var_free_msg n t1)
| nc t1  => (var_free_msg n t1)
| to t1 => (var_free_msg n t1) 
| reveal t1 => (var_free_msg n t1)
| sign t1 t2 => (orb (var_free_msg n t1) (var_free_msg n t2))
| i n' => true
| f  l => (@forallb message (var_free_msg n) l)

end.

(*check if a variable occur in a term of type oursum*)

Definition var_free_os (n:nat) (t:oursum) : bool :=
match t with
| msg t1 => (var_free_msg n t1)
| bol b1 => (var_free_bol n b1)
end.
(*check if mylist contain a variable in one of the element*)

Fixpoint var_free_mylist (n:nat) {m} (l:mylist m) : bool :=
match l with
| [] => false
| h :: t => (orb (var_free_os n h) (var_free_mylist n t))
end.

(*concatenation of two mylists ********)
Fixpoint app_mylist {n1} {n2}  (ml1 : mylist n1) (ml2 : mylist n2) : mylist (plus n1 n2) :=
    match ml1 in (ilist _ n1) return (ilist _ (n1 + n2)) with
      | [] => ml2
      | Cons n1 x ml3 => Cons _ _ x (app_mylist ml3  ml2 )
    end.
Notation "ml1 ++ ml2 " := (app_mylist  ml1 ml2) (at level 60, right associativity).

Eval compute in app_mylist [bol TRue ; bol TRue] [msg (N 0) ; bol TRue] . 


(*check for absence of a variable***)
Fixpoint notoccur_bol (n : nat )(t:Bool) : bool :=
 match t with 
| Bvar n' => true
| FAlse => true
| TRue => true
| EQ_B  b1 b2 =>  andb (notoccur_bol n b1)  (notoccur_bol n b2)
| EQ_M t1 t2 => andb (notoccur_msg n t1) ( notoccur_msg n t2)
| if_then_else_B t1 t2 t3 => andb ( notoccur_bol n t1)  (andb (notoccur_bol n t2)(notoccur_bol n t3) )
| EQL t1 t2 => andb ( notoccur_msg n t1) ( notoccur_msg n t2)
| ver t1 t2 t3 => (andb  (andb (notoccur_msg n t1) (notoccur_msg n t2)) (notoccur_msg n t3))

 end
with notoccur_msg (n : nat )(t:message) : bool :=
 match t with 
| if_then_else_M b3 t1 t2 => andb (notoccur_bol n b3) (andb ( notoccur_msg n  t1)( notoccur_msg n t2))
| (Mvar n') => true
| O => true
| acc => true
| lnc => true
| lsk => true
| N n'=> if (beq_nat n' n) then false else true
| new => true
| exp t1 t2 t3 =>  (andb ( notoccur_msg n t1) (andb ( notoccur_msg n t2) ( notoccur_msg n t3)))
| pair t1 t2 => andb( notoccur_msg n t1) ( notoccur_msg n t2)
| pi1 t1 => ( notoccur_msg n t1)
| pi2 t1 => ( notoccur_msg n t1)
| ggen t1 => ( notoccur_msg n t1)
| act t1 => ( notoccur_msg n t1)
| rr t1 => ( notoccur_msg n t1)
| rs t1 => (notoccur_msg n t1)
| L t1 => (notoccur_msg n t1)
| m t1 => ( notoccur_msg n t1)
| enc t1 t2 t3 =>  andb ( notoccur_msg n t1) (andb ( notoccur_msg n t2) ( notoccur_msg n t3))
| dec t1 t2 => andb( notoccur_msg n t1) ( notoccur_msg n t2)
| k t1 => ( notoccur_msg n t1)
| nc t1 =>  ( notoccur_msg n t1)
| to t1 => (notoccur_msg n t1) 
| reveal t1 => (notoccur_msg n t1)
| sign t1 t2 => (andb (notoccur_msg n t1) (notoccur_msg n t2))
| i n' => true
| f l => (@forallb message (notoccur_msg n) l)

end.
 

Eval compute in (notoccur_msg 1 (pi2 (N 2))).

(*check if absence of a variable in a term of oursum*)

Definition  notoccur_os (n:nat)(t:oursum): bool :=
match t with 
| bol b => notoccur_bol n b 
| msg t => notoccur_msg n t
end.


(**** check if absence of a variable in ilist ********)

Fixpoint notoccur_mlist (x:nat) {n} (ml : ilist message n):bool :=
match ml with
| [] => true
|  h:: ml1 => (andb (notoccur_msg x h) (notoccur_mlist x ml1))
end.
(**** check if absence of a variable in ilist ********)

Fixpoint notoccur_blist {m:nat}(x:nat) (ml : ilist Bool m):bool :=
match ml with
| [] => true
| h :: ml1 => (andb (notoccur_bol x h) (notoccur_blist x ml1))
end.

(**** check if absence of a variable in mylist ********)

Fixpoint notoccur_mylist {m:nat}(x:nat) (ml :  mylist m):bool :=
match ml with
| [] => true
| h :: ml1 => (andb (notoccur_os x h) (notoccur_mylist x ml1))
end.

(***no of occurences of an element in ilist *****************)

 Fixpoint count_occur {n:nat} (x : nat)(l : ilist nat n) : nat :=
    match l with
      | [] => 0
      | y::t =>  if (beq_nat y x) then S (count_occur x t) else (count_occur x t)
    end.
Eval compute in (count_occur 1 [1;1;1]).

(***Check if no redundancies in ilist**************************)

Fixpoint nodup_ilist {n:nat}(l:ilist nat n): bool :=
match l with
|Nil => true
| h::t => let x := (count_occur h (h::t) ) in 
           match (beq_nat x 1) with
           | true => (andb true (nodup_ilist t)) 
            | false => false
             end
end.

Eval compute in (nodup_ilist [1;1]).
Eval compute in (nodup_ilist [1;2;3]).

(****Check if each elt in (ilist nat n) occurs in (ilist message m)*******************)

Fixpoint notocclist_mlist {n:nat} (nl:ilist nat n){m}(ml:ilist message m): bool :=
match nl with
|[] => true
| h::t=> (andb (notoccur_mlist h ml) (notocclist_mlist t ml))
end.

Eval compute in (notoccur_mlist 1 [(N 2);(N 4)]).
Eval compute in True \/ False.

(****Check if each elt in (ilist nat n) occurs in (mylist m)*******************)

Fixpoint notocclist_mylist {n:nat} {m:nat}(nl:ilist nat n)(ml: mylist m): bool :=
match nl with
|[] => true
| h::t=> (andb (notoccur_mylist h ml) (notocclist_mylist t ml))
end.

Eval compute in (notoccur_mylist 1 [msg (N 2); msg (N 4)]).





(****Check if an element occurs in ilist*********************)

 Fixpoint notoccur_nlist {n:nat}(a:nat) (l:ilist nat n) : bool :=
    match l with
      | Nil => true
      | h::t =>   if (beq_nat h a) then false else (andb true (notoccur_nlist a t) )
    end.
Eval compute in (notoccur_nlist 1 [2;3;1]).
Eval compute in (S (pred 1)).

Check beq_nat_refl.


(*Fresh to check if the list of numbers are freshly generated numbers***)

Definition Fresh {n:nat}{m:nat} (nl : ilist nat n)(ml : mylist m): bool :=
match nl with 
| [] => true
| [a] => (notoccur_mylist a ml) 
| l => (andb (nodup_ilist l) (notocclist_mylist l ml) )
end. 

Check beq_nat.

Eval compute in (g 1).
(***************Check if an exp term (exp (G n) (g n) (r n1)) occurs in a term**********)

Fixpoint occexp_in_bol (n : nat ) (n1:nat ) (t:Bool) : bool :=
 match t with 
| Bvar n' => false
| FAlse => false
| TRue => false
| EQ_B  b1 b2 =>  orb (occexp_in_bol n n1 b1)  (occexp_in_bol n n1 b2)
| EQ_M t1 t2 => orb (occexp_in_msg n n1 t1) ( occexp_in_msg n n1 t2)
| if_then_else_B t1 t2 t3 => orb ( occexp_in_bol n n1 t1)  (orb (occexp_in_bol n n1 t2)(occexp_in_bol n n1 t3) )
| EQL t1 t2 => orb ( occexp_in_msg n n1 t1) ( occexp_in_msg n n1 t2)
| ver t1 t2 t3 => (orb  (orb (occexp_in_msg n n1 t1) (occexp_in_msg n n1 t2)) (occexp_in_msg n n1 t3))

 end
with occexp_in_msg (n : nat ) (n1:nat) (t:message) : bool :=
 match t with 
| if_then_else_M b3 t1 t2 => orb (occexp_in_bol n n1 b3) (orb ( occexp_in_msg n n1  t1)( occexp_in_msg n n1 t2))
| (Mvar n') => false
| O => false
| acc => false
| N n'=> false
| lnc => false 
| lsk => false
| new => false
| exp t1 t2 t3 =>  match (t1 , t2 , t3) with 
                       |  ( (pi1 (ggen (N n'))),  (pi2 (ggen (N n''))), (rr (N n'''))) => (andb (beq_nat n n') (andb (beq_nat n n'') (beq_nat n n''')))
                       | _ => false
                  end


 
| pair t1 t2 => orb( occexp_in_msg n n1 t1) ( occexp_in_msg n n1 t2)
| pi1 t1 => ( occexp_in_msg n n1 t1)
| pi2 t1 => ( occexp_in_msg n n1 t1)
| ggen t1 => ( occexp_in_msg n n1 t1)
| act t1 => ( occexp_in_msg n n1 t1)
| rr t1 => ( occexp_in_msg n n1 t1)
| rs t1 => (occexp_in_msg n n1 t1)
| L t1 => (occexp_in_msg n n1 t1)
| m t1 => ( occexp_in_msg n n1 t1)
| enc t1 t2 t3 =>  orb ( occexp_in_msg n n1 t1) (orb ( occexp_in_msg n n1 t2) ( occexp_in_msg n n1 t3))
| dec t1 t2 => orb( occexp_in_msg n n1 t1) ( occexp_in_msg n n1 t2)
| k t1 => ( occexp_in_msg n n1 t1)
| nc t1 =>( occexp_in_msg n n1 t1)
 | to t1 => (occexp_in_msg n n1 t1) 
| reveal t1 => (occexp_in_msg n n1 t1)
| sign t1 t2 => (orb (occexp_in_msg n n1 t1) (occexp_in_msg n n1 t2))
| i n' => true
| f  l => (@existsb message (occexp_in_msg n n1) l)

end.
 



(*Check for given term (exp (G n) (g n) (r n1)) occurs in oursum ********)


Definition  occexp_in_os (n:nat)(n1:nat) (t:oursum): bool :=
match t with 
|bol b => occexp_in_bol n n1 b 
|msg t => occexp_in_msg n n1 t
end.


(**** Check for exp term in a message********)

Fixpoint occexp_in_listm (n n1:nat) (l: list message):bool :=
match l with
| nil => true
|  cons h tl => (orb (occexp_in_msg n n1 h) (occexp_in_listm n n1 tl))
end.



(**** Check for exp term in mylist **)

Fixpoint occexp_in_mylist (n n1:nat) {m} (l: mylist m):bool :=
match l with
| [] => true
|  h::tl => (orb (occexp_in_os n n1 h) (occexp_in_mylist n n1 tl))
end.

(*get an elt at a pos in mylist**)

Fixpoint getelt_at_pos (p :nat) {m}   (ml : mylist m ) : oursum :=
match (leb p m), p with 
| false, _  => msg O
| true, 0 => msg O
| true, 1  => match ml with 
                | [] => msg O
                | h :: t => h
                    end
| true,  (S n') => match ml with
                           | [] => (msg O)
                           | h :: t => (getelt_at_pos n' t)
             end
end.


        
(*get an elt at a pos in ilist **)

Fixpoint getelt_ml {m}  (p :nat) (ml : ilist message m) : message :=
match p with 
| 0 => O
| 1 => match ml with  
       | [] => O
       | h :: t => h
        end
| (S n') => match ml with
              | Nil => O
              | h :: t => (getelt_ml   n' t)
             end
end.

(*appending an elt to mylist at front*)

Fixpoint app_elt_front (x:oursum) {n} (ml: mylist n) : mylist ( S n):=
match ml with
| [] => [x]
| ml3 => (app_mylist [x] ml3)
end.

Notation " x +++ m1 " := (app_elt_front x m1)(at level 0, right associativity).



Eval compute in getelt_at_pos  2 [bol (Bvar 1) ; bol (Bvar 2); msg (N 1); msg (N 2); msg (N 3)].


(*appending an elt of mylist at rear*)
Fixpoint app_elt_last (x:oursum) {n} (ml: mylist n) : mylist ( S n):=
match ml with
| [] => [x]
| h::ml3 => h :: (app_elt_last x ml3)
end.
(*reversing mylist*******)
 Fixpoint reverse {n}(ml: mylist n) : mylist n :=
    match ml with
      | [] => []
      | x :: ml' => (app_elt_last x (reverse ml') )
    end.


(*insert an elt at given position*)
Fixpoint insert_at_pos (p:nat) (x:oursum) {n} (l:mylist n) : mylist (S n) :=
match (leb p n) , p with
| false, _ => (app_elt_last (msg O) l)
| true, 0  =>  (app_elt_last (msg O) l)
| true, 1 => (app_elt_front x l)
| true , (S n') => match l with
                   | [] => [x]
                   | h :: t => (app_mylist [h] (insert_at_pos n' x t))
                   end
end.

Eval compute in (insert_at_pos 5 (msg O) [msg O; msg new ; msg acc; msg O]).

(*check if the term at pos is bool *)

Definition chkbol_at_pos  {m} (n :nat) (ml :mylist m) : bool := (chkbol_os (getelt_at_pos  n ml)).

(*check if the term at pos is message *)
Definition chkmsg_at_pos  {m} (n :nat) (ml :mylist m) : bool := (chkmsg_os (getelt_at_pos n ml)).


(*negating an elt at given position in mylist***)

Definition neg_at_pos {m}   (p:nat ) (ml : mylist m) : mylist 1 :=

match  (chkbol_os (getelt_at_pos p ml)) with
| true => [bol (notb (ostobol (getelt_at_pos p ml)))]
| false =>  [(getelt_at_pos p ml)]
end .

Eval compute in neg_at_pos  2  [bol (Bvar 1) ; bol (Bvar 2); msg (N 1); msg (N 2); msg (N 3)].

(*pairing two elements from mylist*)

Definition pair_at_pos {m}  (p1 p2 : nat) (ml : mylist m) : message :=

match (chkmsg_os (getelt_at_pos  p1 ml)) with
| true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
           | true => (pair (ostomsg (getelt_at_pos  p1 ml)) (ostomsg (getelt_at_pos  p2 ml)))
           | false => (pair (ostomsg  (getelt_at_pos  p1 ml)) O)
           end
| false => match (chkmsg_os (getelt_at_pos  p2 ml)) with
           | true => (pair O (ostomsg (getelt_at_pos  p2 ml)))
           | false => (pair O O)
           end
end.


(*constructing exp term with three terms at positions p1, p2, and p3 in mylist *)
Definition exp_at_pos {m} (p1 p2 p3 :nat) (ml :mylist m) : message :=
match (chkmsg_os (getelt_at_pos  p1 ml)) with
| true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
         | true =>  match (chkmsg_os (getelt_at_pos  p3 ml)) with
                    | true => (exp (ostomsg (getelt_at_pos p1 ml)) (ostomsg (getelt_at_pos  p2 ml))  (ostomsg (getelt_at_pos  p3 ml)) )        
                    | flase => (exp (ostomsg (getelt_at_pos  p1 ml)) (ostomsg (getelt_at_pos  p2 ml))   O )        
                      end
         | false =>   match (chkmsg_os (getelt_at_pos  p3 ml)) with
                    | true => (exp (ostomsg (getelt_at_pos  p1 ml)) O (ostomsg (getelt_at_pos  p3 ml)) )        
                    | flase => (exp (ostomsg (getelt_at_pos  p1 ml)) O   O )        
                      end
          end 

| false =>  match (chkmsg_os (getelt_at_pos  p2 ml)) with
         | true =>  match (chkmsg_os (getelt_at_pos  p3 ml)) with
                    | true => (exp O (ostomsg (getelt_at_pos  p2 ml))  (ostomsg (getelt_at_pos  p3 ml)) )        
                    | flase => (exp O (ostomsg (getelt_at_pos  p2 ml))   O )        
                      end
         | false =>   match (chkmsg_os (getelt_at_pos  p3 ml)) with
                    | true => (exp O O (ostomsg (getelt_at_pos  p3 ml)) )        
                    | flase => (exp O  O   O )        
                      end
          end 
end.

Eval compute in exp_at_pos  3 4 4  [bol (Bvar 1) ; bol (Bvar 2); msg (N 1); msg (N 2); msg (N 3)].

(*constructing a EQ_M term in with the elements in mylist*)

Definition EQ_M_at_pos {m}  (p1 p2 : nat) (ml : mylist m) : Bool :=
match (chkmsg_os (getelt_at_pos  p1 ml)) with
| true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
         | true => (EQ_M (ostomsg (getelt_at_pos  p1 ml)) (ostomsg (getelt_at_pos  p2 ml)))
         | false => (EQ_M (ostomsg (getelt_at_pos  p2 ml)) O)
          end
| false => match (chkmsg_os (getelt_at_pos p2 ml)) with
         | true => (EQ_M O (ostomsg (getelt_at_pos  p2 ml)))
         | false => (EQ_M O O)
         end
end.
(*constructing a EQ_B term in with the elements in mylist*)

Definition EQ_B_at_pos {m}(p1 p2 : nat) (ml : mylist m) : Bool :=
match (chkbol_os (getelt_at_pos  p1 ml)) with
| true => match (chkbol_os (getelt_at_pos  p2 ml)) with
         | true => (EQ_B (ostobol (getelt_at_pos  p1 ml)) (ostobol (getelt_at_pos  p2 ml)))
         | false => (EQ_B (ostobol (getelt_at_pos  p1 ml)) TRue)
          end
| false => match (chkbol_os (getelt_at_pos  p2 ml)) with
         | true => (EQ_B TRue (ostobol (getelt_at_pos  p2 ml)))
         | false => (EQ_B TRue TRue)
         end
end.

(*constructing a andB term in with the elements in mylist*)

Definition andB_at_pos {m} (p1 p2 : nat) (ml : mylist m) : Bool :=
match (chkbol_os (getelt_at_pos  p1 ml)) with
| true => match (chkbol_os (getelt_at_pos  p2 ml)) with
         | true => (andB (ostobol (getelt_at_pos  p1 ml)) (ostobol (getelt_at_pos  p2 ml)))
         | false => (andB (ostobol (getelt_at_pos  p1 ml)) TRue)
          end
| false => match (chkbol_os (getelt_at_pos  p2 ml)) with
         | true => (andB TRue (ostobol (getelt_at_pos  p2 ml)))
         | false => (andB TRue TRue)
         end
end.
(*negating an elt at position in mylist*)

 Definition notB_at_pos {m} (p : nat) (ml : mylist m) : Bool :=
match (chkbol_os (getelt_at_pos  p ml)) with
| true =>  notb (ostobol (getelt_at_pos  p ml))
          
| false => notb (TRue)
end.


(*construction if_then_else_M term from mylist*)

Definition IfM_at_pos {m}  (p1 p2 p3 p4 :nat)(ml : mylist m) : message :=
match (chkbol_os (getelt_at_pos  p1 ml)) with 
| true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
        | true => match (chkmsg_os (getelt_at_pos  p3 ml)) with
                 | true =>  (if_then_else_M (ostobol (getelt_at_pos  p1 ml)) (ostomsg (getelt_at_pos  p2 ml))  ((ostomsg (getelt_at_pos  p3 ml))))
                 | false => (if_then_else_M (ostobol (getelt_at_pos  p1 ml)) (ostomsg (getelt_at_pos  p2 ml)) O)
                    end
        | false =>  match (chkmsg_os (getelt_at_pos  p3 ml)) with
                 | true =>  (if_then_else_M (ostobol (getelt_at_pos  p1 ml)) O ((ostomsg (getelt_at_pos  p3 ml))))
                 | false => (if_then_else_M (ostobol (getelt_at_pos  p1 ml)) O  O)
                    end
            end
| false =>  match (chkmsg_os (getelt_at_pos  p2 ml)) with
        | true => match (chkmsg_os (getelt_at_pos  p3 ml)) with
                 | true =>  (if_then_else_M TRue (ostomsg (getelt_at_pos  p2 ml))  ((ostomsg (getelt_at_pos  p3 ml))))
                 | false => (if_then_else_M TRue (ostomsg (getelt_at_pos  p2 ml)) O)
                    end
        | false =>  match (chkmsg_os (getelt_at_pos  p3 ml)) with
                 | true =>  (if_then_else_M TRue O ((ostomsg (getelt_at_pos  p3 ml))))
                 | false => (if_then_else_M TRue O  O)
                           end
           end
                
end.

(*construction if_then_else_B with terms in mylist**)

Definition IfB_at_pos {m}  (p1 p2 p3 p4 :nat)(ml : mylist m) : Bool :=
match (chkbol_os (getelt_at_pos  p1 ml)) with 
| true => match (chkbol_os (getelt_at_pos  p2 ml)) with
        | true => match (chkbol_os (getelt_at_pos  p3 ml)) with
                 | true =>  (if_then_else_B (ostobol (getelt_at_pos  p1 ml)) (ostobol (getelt_at_pos  p2 ml))  ((ostobol (getelt_at_pos  p3 ml))))
                 | false => (if_then_else_B (ostobol (getelt_at_pos  p1 ml)) (ostobol (getelt_at_pos  p2 ml)) TRue)
                    end
        | false =>  match (chkbol_os (getelt_at_pos  p3 ml)) with
                 | true =>  (if_then_else_B (ostobol (getelt_at_pos  p1 ml)) TRue ((ostobol (getelt_at_pos  p3 ml))))
                 | false => (if_then_else_B (ostobol (getelt_at_pos  p1 ml)) TRue  TRue)
                    end
            end
| false =>  match (chkbol_os (getelt_at_pos  p2 ml)) with
        | true => match (chkbol_os (getelt_at_pos  p3 ml)) with
                 | true =>  (if_then_else_B TRue (ostobol (getelt_at_pos  p2 ml))  ((ostobol (getelt_at_pos  p3 ml))))
                 | false => (if_then_else_B TRue (ostobol (getelt_at_pos  p2 ml)) TRue)
                    end
        | false =>  match (chkbol_os (getelt_at_pos  p3 ml)) with
                 | true =>  (if_then_else_B TRue TRue ((ostobol (getelt_at_pos  p3 ml))))
                 | false => (if_then_else_B TRue TRue TRue)
                           end
           end
                
end.

(*constructing a pair term from mylist**)
Definition pair_term_pos {n}  (m:message) (p:nat)  (ml : mylist n): message :=
(pair m (ostomsg (getelt_at_pos  p ml))).
(******************(If_then_else_M b1 m1 <<m1 , m2> ,m3> : b1 at n1, m1 at n2, m2 at n3, m3 at n4)****************)


Definition ifm_nespair {m}  (p1 p2 p3 p4 :nat)(ml : mylist m) : message := 
match (chkbol_os (getelt_at_pos  p1 ml)) with 
| true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
        | true => if_then_else_M  (ostobol (getelt_at_pos  p1 ml)) (ostomsg (getelt_at_pos  p2 ml))  (pair_term_pos  (pair_at_pos  p2 p3 ml) p4 ml)
        | false => (if_then_else_M  (ostobol (getelt_at_pos  p1 ml)) O (pair_term_pos  (pair_term_pos  O p3 ml) p4 ml))
 end
|false => match (chkmsg_os (getelt_at_pos  p2 ml)) with
        | true => (if_then_else_M  TRue (ostomsg (getelt_at_pos  p2 ml))  (pair_term_pos  (pair_at_pos  p2 p3 ml) p4 ml))
        | false => (if_then_else_M  TRue  O (pair_term_pos  (pair_term_pos  O p3 ml)  p4 ml))
 end
end.



Eval compute in ifm_nespair  1 3 4 5  [bol (Bvar 1) ; bol (Bvar 2); msg (N 1); msg (N 2); msg (N 3)].





(******************(If_then_else_M b1 m1 <m2 ,m3> : b1 at n1, m1 at n2, m2 at n3, m3 at n4)****************)


Definition ifm_pair {m}  (p1 p2 p3 p4 :nat)(ml : mylist m) : message := 
match (chkbol_os (getelt_at_pos  p1 ml)) with 
| true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
        | true => (if_then_else_M  (ostobol (getelt_at_pos  p1 ml)) (ostomsg (getelt_at_pos  p2 ml)) (pair_at_pos  p3 p4 ml))
        | false => (if_then_else_M  (ostobol (getelt_at_pos  p1 ml)) O  (pair_at_pos  p3 p4 ml))
 end
|false => match (chkmsg_os (getelt_at_pos  p2 ml)) with
        | true => (if_then_else_M  TRue (ostomsg (getelt_at_pos  p2 ml))  (pair_at_pos  p3 p4 ml))
        | false => (if_then_else_M  TRue  O  (pair_at_pos  p3 p4 ml))
 end
end.

            
Eval compute in ifm_pair 1 2 3 4  [bol (Bvar 1) ; bol (Bvar 2); msg (N 1); msg (N 2); msg (N 3)].  
(*dropping the last elt in mylist*)
Definition dropone {n:nat} (m:mylist n):(mylist (pred n)):=
match m with 
| [] => []
|  h:: m1 => m1
end.
(*dropping last two elements in a mylist*)
Definition  droptwo {n:nat} (ml: mylist n): mylist (pred (pred n)):= (dropone (dropone ml)).


(**apply reveal at position in mylist*)


Definition reveal_at_pos{m} (p:nat) (ml: mylist m) : message :=
match (chkmsg_os (getelt_at_pos  p ml)) with
| true =>  reveal (ostomsg (getelt_at_pos p ml) )
| false => reveal O
end.
(**apply to at position in mylist*)
Definition to_at_pos {m} (p:nat) (ml: mylist m) : message :=
match (chkmsg_os (getelt_at_pos  p ml)) with
| true =>  to (ostomsg (getelt_at_pos  p ml) )
| false => to O
end.
(**apply act at position in mylist*)
Definition act_at_pos {m} (p:nat) (ml: mylist m) : message :=
match (chkmsg_os (getelt_at_pos  p ml)) with
| true =>  act (ostomsg (getelt_at_pos  p ml) )
| false => act O
end.
(**apply m at position in mylist*)
Definition m_at_pos {n} (p:nat) (ml:mylist n) : message :=
match (chkmsg_os (getelt_at_pos p ml)) with
| true =>  m (ostomsg (getelt_at_pos p ml) )
| false => m O
end.

Eval compute in to_at_pos 4 [bol (Bvar 1) ; bol (Bvar 2); msg (N 1); msg (N 2); msg (N 3)]. 

  
 
(**********constant function "const" definition*************************)
(***********************************************************************)

Definition const {X:Type}{Y:Type}(a : X) := fun _ : Y => a.
Eval compute in (const (N 0) O ).


(***substitute Bool in  mylist************************************************)
(*****************************************************************************)

Fixpoint subbol_mylist {n1:nat} (n:nat)(s:Bool)(ml: mylist n1):mylist n1 :=
match ml with 
| Nil => []
| h::t => (subbol_os n s h) :: (subbol_mylist n s t)
end.
(***substitute message in  mylist************************************************)
(********************************************************************************)

Fixpoint submsg_mylist {n1:nat} (n:nat)(s:message)(ml: mylist n1):mylist n1 :=
match ml with 
| Nil => []
| h::t => (submsg_os n s h) :: (submsg_mylist n s t)
end.

Eval compute in (subbol_mylist 1 TRue [msg O; msg (Mvar 1); bol (Bvar 1)]).
Eval compute in (submsg_os 1  ( O) (bol (Bvar 1))).






Definition drpone_last {n} (l:mylist (S n)) : mylist n :=  dropone(reverse l).




(****************SOME FUNCTIONS************************************)



Definition proj_one {n} (l: mylist n) : mylist 1:=
match (reverse   l)  with
| [] => [msg O]
| h::t => [h]
end.

(*****************drop second elt from last*********************************)
Definition proj_two {n} (l:mylist n) : mylist 2:=
match (reverse l) with
|[] => [msg O; msg O]
| h::t::l' => [t;h]
| h:: t => [msg O; h]

end.



Definition droplastsec {n} (l:mylist n) : mylist (pred (pred n) + pred 2) :=
let y := (proj_two l) in
let x := (droptwo (reverse l)) in
let y1:= (dropone y) in 
(app_mylist (reverse x) y1).
Eval compute in (droplastsec  [msg O; msg (Mvar 1)]).

(*************************drop third elt from last***********************************************)
Definition proj_three {n} (l: mylist n) : mylist 3:=
match (reverse l) with 
| [] => [msg O ; msg O ; msg O]
| h :: h1 :: h2 :: l1 => [h2 ; h1 ; h]
| h :: h1 :: t => [ msg O; h1 ; h]
| h :: t => [msg O ; msg O ; h]
end.

Definition droplast3rd {n} (l:mylist n) : mylist (( pred (pred (pred n) ) ) + pred 3) :=
let y := (proj_three l) in 
let x := (dropone (droptwo (reverse l))) in
let y1 := (dropone y) in 
(app_mylist (reverse x) y1)
.
Eval compute in (droplast3rd  [ msg (Mvar 1)]).

(**********************to get mylist n of elt msg O***********************)
Fixpoint app_n_elts (n:nat) :mylist n :=
match n with
| 0 => []
| S n' => (app_mylist (app_elt_front (msg O) []) (app_n_elts n'))
end.

Eval compute in app_n_elts 3.

(****************apply pred n times on m*********************************)
Fixpoint app_pred_n (n m:nat) : nat :=
match n with 
| 0 => m
| S n' => (app_pred_n n' (pred m))
end.

(***************************************drop n elements from mylist m*********)
Fixpoint drop_n_times (n :nat) {m} (l:mylist m) : mylist (app_pred_n n m) :=
match (leb n m) with 
| true => match n with
           | 0 => l
           | S n' => let x := (dropone l) in
                         drop_n_times n' x
             end
| false => app_n_elts (app_pred_n n  m)
end.  
Eval compute in drop_n_times 5 [msg O; msg O; msg O; msg O].


Definition Firstn (n:nat) {m} (l: mylist m) : mylist (app_pred_n (app_pred_n n  m) m) :=  reverse (drop_n_times (app_pred_n n m ) (reverse l)).
Definition Skipn (n:nat) {m} (l: mylist m) : mylist (app_pred_n n m) :=  drop_n_times n l.

Eval compute in Skipn 3 [msg (Mvar 4); msg (Mvar 3); msg (Mvar 2); msg (Mvar 1)].
Eval compute in Firstn 0 [msg (Mvar 4); msg (Mvar 3); msg (Mvar 2); msg (Mvar 1)].
Eval compute in Firstn 1 [msg (Mvar 4); msg (Mvar 3); msg (Mvar 2); msg (Mvar 1)].
Eval compute in Skipn 5 [msg (Mvar 4); msg (Mvar 3); msg (Mvar 2); msg (Mvar 1)].
Eval compute in  (dropone (Skipn (app_pred_n 1 2 ) (dropone (Skipn 1 [msg (Mvar 4); msg (Mvar 3); msg (Mvar 2); msg (Mvar 1)])))).
(******************************swap two elements *********************************)

Definition swap_mylist (p1 p2 :nat) {m} (l:mylist m) : mylist
    (pred (app_pred_n (app_pred_n p1 m) m) +
     (1 +
      (pred
         (app_pred_n (app_pred_n (app_pred_n p1 p2) (app_pred_n p1 m))
            (app_pred_n p1 m)) +
       (1 + app_pred_n (app_pred_n p1 p2) (app_pred_n p1 m))))) :=
let x := (Firstn p1 l) in 
let y := (Skipn p1 l) in 
let x1 := (proj_one x) in 
let x2 := reverse (dropone (reverse x)) in
let x3 := (Firstn (app_pred_n p1 p2 ) y) in
let x4 :=  (Skipn (app_pred_n p1 p2) y) in
let x5 := (proj_one x3) in
let x6 := reverse (dropone (reverse x3)) in 
x2 ++ x5 ++ x6 ++ x1 ++ x4.

Eval compute in swap_mylist 1 3  [ msg O; msg (Mvar 3); msg (Mvar 2); msg (Mvar 1)].


(*****************************proj an elt at position p *****************************)


Definition proj_at_pos (p:nat) {m} (l:mylist m) : mylist (pred (app_pred_n (app_pred_n p m) m) + app_pred_n p m) :=
let x := (Firstn p l) in
let y := (Skipn p l) in
let x1 := reverse (dropone (reverse x)) in

x1 ++ y.


Eval compute in proj_at_pos 3  [ msg O; msg (Mvar 3); msg (Mvar 2); msg (Mvar 1)].



(***********************************************************************************************)
(************************************************************************************************)




(**
Fixpoint map1 {X :Type} {f1: message->message->bool}(f:X -> X -> bool) (l:list X)  : bool :=
  match l with
  | nil => true
  | cons h t => (andb (f h h)  (map1 f t))
  end.

Fixpoint eq_list {f1: message -> message -> bool} l := fix pair1  (l':list message)   :=
*)



(*****************Check if two terms are equal *****************************************************)
(***************************************************************************************************)

Check map.
Check max. 
(*
Section size_listrms.

Variable f:  nat -> message   -> nat.
Fixpoint size_listrms (n:nat) (l :list message) :nat :=
match l with 
| nil => n
| cons h t =>  (size_listrms (f n h)  t)
end.
End size_listrms.


Fixpoint size_bol  (n:nat) (b :Bool) : nat :=
match b with 
| Bvar n' => (S n)
| FAlse =>  (S n)
| TRue => (S n)
| EQ_B b1 b2 => S (size_bol (size_bol n  b1)  b2)
| EQ_M t1 t2 => S (size_msg (size_msg n t1)  t2)
| EQL t1 t2 =>   S (size_msg (size_msg n  t1)  t2)
| if_then_else_B b1 b2  b3 =>  S  (size_bol (size_bol (size_bol n b1) b2) b3)
| ver t1 t2 t3 =>   S  (size_msg (size_msg (size_msg n t1) t2) t3)
end
with size_msg (n:nat) ( t : message ) : nat :=
 match t with 
| Mvar n => (S n)
| O => (S n)
 
| acc => (S n)
| N n'=>  (S n)

| if_then_else_M b1 t1 t2 =>  S  (size_msg (size_msg (size_bol n b1) t1) t2)
| exp t1 t2 t3 =>   S  (size_msg (size_msg (size_msg n t1) t2) t3)

| pair t1 t2 => S (size_msg (size_msg n t1)  t2)
               
                  
| pi1 t1 => S (size_msg n t1) 
                
| pi2 t1 => S (size_msg n t1) 
            
| ggen t1 =>  S (size_msg n t1) 
 |rr t1 =>  S (size_msg n t1) 
| new => (S n)
          
| act t1 => S (size_msg n t1) 
| m t1 =>  S (size_msg n t1) 
           

| nc t1 =>( S n)
|rs t1 =>  S (size_msg n t1) 
          
|L t1 => S (size_msg n t1)       

           
| enc t1 t2 t3 =>  S  (size_msg (size_msg (size_msg n t1) t2) t3)
                
                
                
 |dec t1 t2 =>  S (size_msg (size_msg n t1)  t2)
                   
|k t1 =>  S (size_msg n t1)    
         
        
             
| to t1 =>  S (size_msg n t1)       
           
           
| reveal t1 =>   S (size_msg n t1)       
               
| sign t1 t2 =>    S (size_msg (size_msg n t1)  t2)
               
| i n' =>  (S n)
          
          
| f l =>  S (@size_listrms (size_msg ) n l)
            
 end.
*)


Section def.
Variable A B :Type. 
Variable  f: message -> message -> bool.
Fixpoint check_eq_listm  (l l' :list message)  :bool :=
    match l  with
              | nil => match l' with
                    | nil => true
                    | _ => false
                         end  
   
              | cons h t =>  match l' with
                         | cons h' t' => (andb (f h h') (check_eq_listm t t'))
                         | _ => false
                            end
end.


End def.
Print check_eq_listm.
Eval compute in O = O.
Eval compute in O = (N 1). 


Fixpoint check_eq_bol (b b': Bool) : bool :=
 match b with 
         | Bvar n' => match b' with 
                      | (Bvar n'') => if (beq_nat n' n'') then true else false
                      | _ => false
                       end
         | FAlse => match b' with 
                   | FAlse => true 
                   | _ => false
                    end
         | TRue => match b' with 
                  | TRue => true
                  | _ => false 
                    end
         | EQ_B b1 b2 => match b' with 
                       | EQ_B b3 b4 => (andb (check_eq_bol b1 b3) (check_eq_bol b2 b4))
                       | _ => false
                        end
         | EQ_M t1 t2 => match b' with 
                          | EQ_M t3 t4 => (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4))
                          | _ => false
                        end
         | EQL t1 t2 => match b' with 
                          | EQL t3 t4 => (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4))
                          | _ => false
                        end
         | (if_then_else_B b1 b2  b3) =>  match b' with 
                            | (if_then_else_B b4 b5 b6) => (andb (check_eq_bol b1 b4) (andb (check_eq_bol b2 b5) (check_eq_bol b3 b6)))
                            | _ => false
                           end
         | ver t1 t2 t3 =>  match b' with
                  | ver t4 t5 t6 => (andb (check_eq_msg t1 t4) (andb (check_eq_msg t2 t5 ) (check_eq_msg t3 t6)))
                 | _ => false
                  end
       end 
 
with check_eq_msg ( t t' : message ) : bool :=
   match t with    
     | Mvar n =>  match t' with 
                    | Mvar n' => (beq_nat n n')
                    | _  => false 
                   end
  
    | O => match t' with
              | O => true
              | _ => false
            end
     | lnc => match t' with
              | lnc => true
              | _ => false
            end
       | lsk => match t' with
              | lsk => true
              | _ => false
            end
     
     | acc => match t' with
                | acc => true
                | _ => false 
              end
     | N n'=>  match t' with
                 | N n'' => if (beq_nat n' n'') then true else false
                 | _ => false 
               end

     | (if_then_else_M b1 t1 t2) =>  match t' with 
                              | (if_then_else_M b2 t3 t4) => (andb (check_eq_bol b1 b2) (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4)))
                            | _ => false
                           end
   | exp t1 t2 t3 =>  match t' with
                        | exp t4 t5 t6 => (andb (check_eq_msg t1 t4) (andb (check_eq_msg t2 t5 ) (check_eq_msg t3 t6)))
                 | _ => false
                  end

   | pair t1 t2 => match t' with
                 | pair t3 t4 => (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4))
                 | _ => false
                end 
               
                  
   | pi1 t1 =>  match t' with
              | pi1 t2 =>  (check_eq_msg t1 t2)
              | _ => false
              end
                
   | pi2 t1 => match t' with
               | pi2 t2 =>  (check_eq_msg t1 t2)

              | _ => false
              end
            
   | ggen t1 =>   match t' with
                 | ggen t2 =>  (check_eq_msg t1 t2)

                 | _ => false
              end
   |rr t1 =>   match t' with
                 | rr t2 =>  (check_eq_msg t1 t2)

                 | _ => false 
               end   
   | new => match t' with 
              | new => true
              | _ => false
            end
          
   | act t1 => match t' with
                 | act t2 =>  (check_eq_msg t1 t2)

                 | _ => false
               end
             
   | m t1 =>   match t' with
                 | m t2 =>  (check_eq_msg t1 t2)
                 | _ => false
             end
           

  | nc t1  =>  
          match t' with
             | nc t2 =>  (check_eq_msg t1 t2)
             | _ => false
             end
   |rs t1 =>   match t' with
             | rs t2 =>  (check_eq_msg t1 t2)
             | _ => false
             end
          
   |L t1 => match t' with
             | L t2 =>  (check_eq_msg t1 t2)
             | _ => false
             end            

           
   | enc t1 t2 t3 =>  match t' with
                 | enc t4 t5 t6 => (andb (check_eq_msg t1 t4) (andb (check_eq_msg t2 t5 ) (check_eq_msg t3 t6)))
                 | _ => false
                  end
                
                
                
   |dec t1 t2 =>  match t' with
                 | dec t3 t4 => (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4))
                 | _ => false
                end 
                   
   |k t1 => match t' with
             | k t2 =>  (check_eq_msg t1 t2)
             | _ => false
             end
         
    
             
   | to t1 => match t' with
             | to t2 =>  (check_eq_msg t1 t2)
             | _ => false
             end
           
           
   | reveal t1 =>   match t' with
                      | reveal t2 =>  (check_eq_msg t1 t2)
                      | _ => false
                    end

               
   | sign t1 t2 =>   match t' with
                 | sign t3 t4 => (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4))
                 | _ => false
                end 
               
   | i n' =>  
          match t' with
             | i n'' => if  (beq_nat n' n'') then true else false
             | _ => false
             end
          
          
   | f l =>   match t' with
             | f l' => ( @check_eq_listm  (check_eq_msg ) l l')
            | _ => false
              end
         
            
   end.



Eval compute in check_eq_msg (f (cons O nil)) (f (cons O (cons O nil))).
Check map.
Eval compute in check_eq_msg O (Mvar 1).
Eval compute in check_eq_msg (if_then_else_M FAlse O (Mvar 1)) (if_then_else_M FAlse (Mvar 2) (Mvar 1)).

Eval compute in (check_eq_listm check_eq_msg (cons O (cons O nil)) (cons O (cons O nil))).

(**********************************************************************************************************************************************)
(**********************************************************************************************************************************************)

(**********check occurence of a term in a term *****************)

Fixpoint occbol_in_bol ( t':Bool) (t:Bool) : bool :=
 match t  with 
| Bvar n'  =>  (check_eq_bol t t')
| FAlse =>  (check_eq_bol t t')
| TRue => (check_eq_bol t t')
| EQ_B  b1 b2 =>  match t' with
                  | EQ_B b3 b4 => (orb (check_eq_bol t' t) (orb (occbol_in_bol t' b1) (occbol_in_bol t' b2)))                                
                  | _ =>  (orb (occbol_in_bol t' b1) (occbol_in_bol t' b2))
                   end
| EQ_M t1 t2 =>  match t' with
                  | EQ_M t3 t4 => (orb (check_eq_bol t' t) (orb (occbol_in_msg t' t1) (occbol_in_msg t' t2)))
                                             | _ =>  (orb (occbol_in_msg t' t1) (occbol_in_msg t' t2))
                   end
| if_then_else_B t1 t2 t3 => match t' with
                              | if_then_else_B t4 t5 t6 => (orb (check_eq_bol t' t) (orb (occbol_in_bol t' t1) (orb (occbol_in_bol t' t2) (occbol_in_bol t' t3))))
                                                       
                              | _ => (orb (occbol_in_bol t' t1) (orb (occbol_in_bol t' t2) (occbol_in_bol t' t3)))
                              end
| EQL t1 t2 =>  match t' with
                  | EQL t3 t4 => (orb (check_eq_bol t t')  (orb (occbol_in_msg t' t1 ) (occbol_in_msg t' t2)))
                 | _ =>  (orb (occbol_in_msg t' t1 ) (occbol_in_msg t' t2))
                  end
| ver t1 t2 t3 =>  match t' with 
                  | ver t4 t5 t6 => (orb (check_eq_bol t' t)  (orb (occbol_in_msg t' t1)  (orb (occbol_in_msg t' t2) (occbol_in_msg t' t3))))
                  | _ => (orb (occbol_in_msg t' t1)  (orb (occbol_in_msg t' t2) (occbol_in_msg t' t3)))
            end
 end
with occbol_in_msg  (t':Bool) (t:message) : bool :=
 match t with 
| if_then_else_M b t1 t2 =>   (orb (occbol_in_bol t' b) (orb (occbol_in_msg t' t1) (occbol_in_msg t' t2)))
| (Mvar n') => false
| O => false
| acc => false
| N n'=> false
|new => false
| lsk => false
| lnc => false
| exp t1 t2 t3 => (orb (occbol_in_msg t' t1) (orb (occbol_in_msg t' t2) (occbol_in_msg t' t3)))

 
| pair t1 t2 => (orb (occbol_in_msg t' t1) (occbol_in_msg t' t2))
| pi1 t1 =>  (occbol_in_msg t' t1) 
| pi2 t1 =>  (occbol_in_msg t' t1) 
| ggen t1 =>  (occbol_in_msg t' t1) 
| act t1 =>   (occbol_in_msg t' t1) 
| rr t1 =>   (occbol_in_msg t' t1) 
| rs t1 =>  (occbol_in_msg t' t1) 
| L t1 =>   (occbol_in_msg t' t1) 
| m t1 =>   (occbol_in_msg t' t1) 
|enc t1 t2 t3 =>   (orb (occbol_in_msg t' t1) (orb (occbol_in_msg t' t2) (occbol_in_msg t' t3)))
|dec t1 t2 => (orb (occbol_in_msg t' t1) (occbol_in_msg t' t2))
| k t1 =>  (occbol_in_msg t' t1) 
| nc t1 => (occbol_in_msg t' t1) 
 | to t1 =>  (occbol_in_msg t' t1) 
| reveal t1 =>  (occbol_in_msg t' t1) 
| sign t1 t2 =>(orb (occbol_in_msg t' t1) (occbol_in_msg t' t2))
| i n' => false
| f  l => (@existsb message (occbol_in_msg t') l)

end.
(**************************check for message***************)

Fixpoint occmsg_in_bol  (t': message) (  t:Bool) : bool :=
 match t  with 
| Bvar n'  => false
| FAlse =>  false
| TRue =>  false
| EQ_B  b1 b2 => (orb (occmsg_in_bol t' b1) (occmsg_in_bol t' b2))  
| EQ_M t1 t2 => (orb (occmsg_in_msg t' t1 ) (occmsg_in_msg t' t2))
| if_then_else_B t1 t2 t3 => (orb (occmsg_in_bol t' t1) (orb (occmsg_in_bol t' t2) (occmsg_in_bol t' t3)))
| EQL t1 t2 => (orb (occmsg_in_msg t' t1 ) (occmsg_in_msg t' t2))  
| ver t1 t2 t3 => (orb (occmsg_in_msg t' t1)  (orb (occmsg_in_msg t' t2) (occmsg_in_msg t' t3)))

 end
with occmsg_in_msg   (t' t:message) : bool :=
 match t with 
| if_then_else_M b t1 t2 =>  match t' with 
                            | if_then_else_M b1 t3 t4 => (orb (andb (check_eq_bol b1 b) (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4)))
                                                          (orb (occmsg_in_bol t' b) (orb (occmsg_in_msg t' t1) (occmsg_in_msg t' t2))))
  | _ => (orb (occmsg_in_bol t' b) (orb (occmsg_in_msg t' t1) (occmsg_in_msg t' t2)))
end
 
| (Mvar n') => (check_eq_msg t t')
               
| O => (check_eq_msg t t')
| lsk => (check_eq_msg t t')
| lnc => (check_eq_msg t t')
| acc => (check_eq_msg t t')
| N n'=> (check_eq_msg t t')
| new => (check_eq_msg t t')
| exp t1 t2 t3 =>  match t' with
                    | exp t4 t5 t6 => (orb (andb (andb (check_eq_msg t1 t4) (check_eq_msg t2 t5)) (check_eq_msg t3 t6)) (orb (occmsg_in_msg t' t1) (orb (occmsg_in_msg t' t2) (occmsg_in_msg t' t3))) )
                                                                           
                    | _ =>  (orb (occmsg_in_msg t' t1) (orb (occmsg_in_msg t' t2) (occmsg_in_msg t' t3)))
                      end
| pair t1 t2 =>  match t' with
                 | pair t3 t4 => (orb (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4)) (orb (occmsg_in_msg t' t1) (occmsg_in_msg t' t2)))
                                    
                 | _ => (orb (occmsg_in_msg t' t1) (occmsg_in_msg t' t2))
                  end
| pi1 t1 =>  match t' with 
               | pi1 t2 =>   (orb (check_eq_msg t1 t2)  (occmsg_in_msg t' t1))
                            
               | _ => (occmsg_in_msg t' t1)
              end
| pi2 t1 =>   match t' with 
               | pi2 t2 => (orb  (check_eq_msg t1 t2)  (occmsg_in_msg t' t1))
               | _ => (occmsg_in_msg t' t1)
              end
| ggen t1 =>  match t' with 
               | ggen t2 => (orb (check_eq_msg t1 t2)  (occmsg_in_msg t' t1))
               | _ => (occmsg_in_msg t' t1)
              end
| act t1 =>  match t' with 
               | act t2 =>  (orb (check_eq_msg t1 t2)  (occmsg_in_msg t' t1))
               | _ => (occmsg_in_msg t' t1)
              end
| rr t1 =>    match t' with 
               | rr t2 =>  (orb (check_eq_msg t1 t2)  (occmsg_in_msg t' t1))
               | _ => (occmsg_in_msg t' t1)
              end
| rs t1 =>   match t' with 
               | rs t2 =>  (orb (check_eq_msg t1 t2)  (occmsg_in_msg t' t1))
               | _ => (occmsg_in_msg t' t1)
              end
| L t1 =>   match t' with 
               | L t2 =>  (orb (check_eq_msg t1 t2)  (occmsg_in_msg t' t1))
               | _ => (occmsg_in_msg t' t1)
              end
| m t1 =>    match t' with 
               | m t2 =>  (orb (check_eq_msg t1 t2)  (occmsg_in_msg t' t1))
               | _ => (occmsg_in_msg t' t1)
              end
| enc t1 t2 t3 =>    match t' with
                    | enc t4 t5 t6 => (orb (andb (andb (check_eq_msg t1 t4) (check_eq_msg t2 t5)) (check_eq_msg t3 t6)) (orb (occmsg_in_msg t' t1) (orb (occmsg_in_msg t' t2) (occmsg_in_msg t' t3))))
                    | _ =>  (orb (occmsg_in_msg t' t1) (orb (occmsg_in_msg t' t2) (occmsg_in_msg t' t3)))
                      end
| dec t1 t2 =>  match t' with
                 | dec t3 t4 => (orb (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4)) (orb (occmsg_in_msg t' t1) (occmsg_in_msg t' t2)))
                 | _ => (orb (occmsg_in_msg t' t1) (occmsg_in_msg t' t2))
                  end
| k t1 =>    match t' with 
               | k t2 =>  (orb (check_eq_msg t1 t2) (occmsg_in_msg t' t1))
               | _ => (occmsg_in_msg t' t1)
              end
| nc t1 =>  match t' with 
               | nc t2 =>  (orb (check_eq_msg t1 t2) (occmsg_in_msg t' t1))
               | _ => (occmsg_in_msg t' t1)
              end
 | to t1 =>   match t' with 
               | to t2 =>  (orb (check_eq_msg t1 t2) (occmsg_in_msg t' t1))
               | _ => (occmsg_in_msg t' t1)
              end
| reveal t1 =>  match t' with 
               | reveal t2 => (orb (check_eq_msg t1 t2) (occmsg_in_msg t' t1))
               | _ => (occmsg_in_msg t' t1)
              end
| sign t1 t2 =>  match t' with
                 | sign t3 t4 => (orb (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4)) (orb (occmsg_in_msg t' t1) (occmsg_in_msg t' t2)))
                 | _ => (orb (occmsg_in_msg t' t1) (occmsg_in_msg t' t2))
                  end
| i n' =>  match t' with 
          | i n'' => if beq_nat n'' n' then true else false
          | _ => false 
            end
| f  l => match t' with 
          | f l1 => (orb ( @check_eq_listm  (check_eq_msg ) l l1) (@existsb message (occmsg_in_msg t') l))
          | _ => (@existsb message (occmsg_in_msg t') l)
          end
end.

Eval compute in occmsg_in_bol O (EQ_M O O)&TRue .


(*****************************substitute term ts (Bool) for a term t'(Bool) *******************************************************************)
(*************************************************************************************************************************************)

(**replace b' with s in b*********)

Fixpoint subbol_bol'  (b' : Bool) (s: Bool) (b :Bool) : Bool :=
match (check_eq_bol b' b) with
| true => s
| false =>
         match b with 
           | Bvar n' =>  match b' with 
                           | Bvar n'' => if (beq_nat n' n'') then s else (Bvar n')
                           | _ => Bvar n'
                         end
           | FAlse => match b' with 
                        | FAlse => s
                        | _ => FAlse 
                      end
           | TRue =>  match b' with
                        | TRue => s
                        | _ => TRue
                      end
           | EQ_B  b1 b2 =>  match b' with 
                               | (EQ_B b3 b4) => if (andb (check_eq_bol b1 b3) (check_eq_bol b2 b4)) then s else  (EQ_B (subbol_bol' b' s b1) (subbol_bol' b' s b2))
                               | _ =>  (EQ_B (subbol_bol' b' s b1) (subbol_bol' b' s b2))
                             end
           | EQ_M t1 t2 =>  match b' with 
                              | EQ_M t3 t4 =>  if (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4)) then s else (EQ_M (subbol_msg' b' s t1) (subbol_msg' b' s t2))
                              | _ => (EQ_M (subbol_msg' b' s t1) (subbol_msg' b' s t2))
                            end
           | if_then_else_B b1 b2 b3 =>  match b' with 
                                           | if_then_else_B b4 b5 b6 => if (andb (check_eq_bol b1 b4) (andb (check_eq_bol b2 b5) (check_eq_bol b3 b6))) then s else (if_then_else_B (subbol_bol' b' s b1) (subbol_bol' b' s b2) (subbol_bol' b' s b3)) 
                                           | _ => (if_then_else_B (subbol_bol' b' s b1) (subbol_bol' b' s b2) (subbol_bol' b' s b3)) 
                                         end
           | EQL t1 t2 => match b' with
                            | EQL t3 t4 =>  if (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4)) then s else (EQL (subbol_msg' b' s t1) (subbol_msg' b' s t2))
                            | _ =>  (EQL (subbol_msg' b' s t1) (subbol_msg' b' s t2))
                          end
           | ver t1 t2 t3 => match b' with 
                               | ver t4 t5 t6 => if (andb (check_eq_msg t1 t4) (andb (check_eq_msg t2 t5) (check_eq_msg t3 t6))) then s else (ver  (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3))
                               | _ => ver  (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)
                             end

         end
end

with subbol_msg' (b' : Bool )(s: Bool) (t:message) : message :=
 match t with 
             | if_then_else_M b t1 t2 =>    (if_then_else_M (subbol_bol' b' s b) (subbol_msg' b' s t1) (subbol_msg' b' s t2))
                                     
             | (Mvar n') =>  (Mvar n')
             | O => O
             | lnc => lnc
             | lsk => lsk
             | acc => acc
             | N n'=>  N n'
             | new => new
             | exp t1 t2 t3 =>   exp  (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)
             | pair t1 t2 => pair (subbol_msg' b' s t1) (subbol_msg' b' s t2)
             | pi1 t1 =>  pi1 (subbol_msg' b' s t1)
             | pi2 t1 =>  pi2 (subbol_msg' b' s t1)
             | ggen t1 =>   ggen (subbol_msg' b' s t1)
             | act t1 =>  act (subbol_msg' b' s t1)
             |rr t1 =>    rr (subbol_msg' b' s t1)
             |rs t1 =>   rs (subbol_msg' b' s t1)
             |L t1 =>  L (subbol_msg' b' s t1)
             | m t1 =>    m (subbol_msg' b' s t1)
             | enc t1 t2 t3 => enc (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)
             | dec t1 t2 => dec  (subbol_msg' b' s t1) (subbol_msg' b' s t2) 
              |k t1 =>  k (subbol_msg' b' s t1)
          | nc t1 =>  nc (subbol_msg' b' s t1)
          | to t1 => to  (subbol_msg' b' s t1) 
          | reveal t1 =>  reveal (subbol_msg' b' s t1) 
          | sign t1 t2 =>   sign (subbol_msg' b' s t1) (subbol_msg' b' s t2) 
          | i n' =>  (i n')      
          | f l =>  (f (@map message message  (subbol_msg' b' s) l))
          end.

Eval compute in subbol_bol' TRue FAlse TRue.
Eval compute in subbol_bol' (EQ_M O (i 1)) FAlse (EQ_B (EQ_M O (i 1)) (EQ_M O (i 1))). 
 
(**********************substitute a term s (message) for a term t' (message) in t ******************************)
(***************************************************************************************************************)
Fixpoint submsg_bol' (t' : message)(s:message) (t:Bool) : Bool :=
 
 match t with 
              | Bvar n' =>  Bvar n'
              | FAlse => FAlse
              | TRue => TRue
              | EQ_B  b1 b2 =>  (EQ_B (submsg_bol' t' s b1) (submsg_bol' t' s b2))
              | EQ_M t1 t2 => (EQ_M (submsg_msg' t' s t1) (submsg_msg' t' s t2))
              | if_then_else_B t1 t2 t3 => (if_then_else_B (submsg_bol' t' s t1) (submsg_bol' t' s t2) (submsg_bol' t' s t3))
              | EQL t1 t2 =>  (EQL (submsg_msg' t' s t1) (submsg_msg' t' s t2))
              | ver t1 t2 t3 => ver  (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3)
            end
with submsg_msg' (t' : message )(s:message) (t:message) : message :=
match (check_eq_msg t' t) with
| true => s
| false => 
          match t with 
            | if_then_else_M b1 t1 t2 =>    match t' with 
                                              | if_then_else_M b2 t3 t4 => if (andb (check_eq_bol b1 b2) (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4))) then s else  (if_then_else_M (submsg_bol' t' s b1) (submsg_msg' t' s t1) (submsg_msg' t' s t2)) 
                                              | _ => (if_then_else_M (submsg_bol' t' s b1) (submsg_msg' t' s t1) (submsg_msg' t' s t2)) 
                                            end
            | (Mvar n') =>   match t' with
                               | Mvar n'' => if (beq_nat n' n'') then s else (Mvar n')
                               | _ => (Mvar n')
                             end
            | O => match t' with
                     | O => s
                     | _ => O
                   end
            | acc => match t' with
                       | acc => s
                       | _ => acc
                     end
             | lsk => match t' with
                       | lsk => s
                       | _ => lsk
                     end
              | lnc => match t' with
                       | lnc => s
                       | _ => lnc
                     end
            | N n'=> match t' with 
                       | N n'' => if (beq_nat n' n'') then s else (N n')
                       | _ => N n'
                     end
            |new => match t' with
                      | new => s
                      | _ => new
                    end
            | exp t1 t2 t3 =>        match t' with 
                                       |    exp t4 t5 t6 => if (andb (check_eq_msg t1 t4) (andb (check_eq_msg t2 t5) (check_eq_msg t3 t6))) then s else   (exp  (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3))
                                       | _ =>    exp  (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3)
                                     end
            | pair t1 t2 => match t' with 
                              | pair t3 t4 => if (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4)) then s else (pair (submsg_msg' t' s t1) (submsg_msg' t' s t2))
                              | _ => pair (submsg_msg' t' s t1) (submsg_msg' t' s t2)
                            end
            | pi1 t1 =>  match t' with 
                           | pi1 t2 =>  if (check_eq_msg t1 t2) then s else  (pi1 (submsg_msg' t' s t1))
                           | _ => pi1 (submsg_msg' t' s t1)
                         end
            | pi2 t1 => match t' with 
                          | pi2 t2 =>  if (check_eq_msg t1 t2) then s else  (pi2 (submsg_msg' t' s t1))
                          | _ => pi2 (submsg_msg' t' s t1)
                        end
            | ggen t1 =>  match t' with
                            | ggen t2 =>  if (check_eq_msg t1 t2) then s else (ggen (submsg_msg' t' s t1))
                            | _ => ggen (submsg_msg' t' s t1)
                          end
            | act t1 => match t' with 
                          | act t2 =>  if (check_eq_msg t1 t2) then s else (act (submsg_msg' t' s t1))
                          | _ =>  act (submsg_msg' t' s t1)
                        end
            |rr t1 => match t' with 
                        | rr t2 =>  if (check_eq_msg t1 t2) then s else (rr (submsg_msg' t' s t1))
                        | _ =>  rr (submsg_msg' t' s t1)
                      end
            |rs t1 =>  match t' with 
                         | rs t2 =>  if (check_eq_msg t1 t2) then s else (rs (submsg_msg' t' s t1))
                         | _ =>  rs (submsg_msg' t' s t1)
                       end
            |L t1 =>  match t' with 
                        | L t2 =>  if (check_eq_msg t1 t2) then s else (L (submsg_msg' t' s t1))
                        | _ =>  L (submsg_msg' t' s t1)
                      end
            | m t1 =>  match t' with 
                         | m t2 =>  if (check_eq_msg t1 t2) then s else  (m (submsg_msg' t' s t1))
                         | _ =>  m (submsg_msg' t' s t1)
                       end
            | enc t1 t2 t3 => match t' with
                                | enc t4 t5 t6 =>    if (andb (check_eq_msg t1 t4) (andb (check_eq_msg t2 t5) (check_eq_msg t3 t6))) then s else ( enc (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3))
                                | _ => enc (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3)
                              end
            |dec t1 t2 =>  match t' with 
                             | dec t3 t4 =>  if (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4)) then s else ( dec  (submsg_msg' t' s t1) (submsg_msg' t' s t2) )
                             | _ => dec  (submsg_msg' t' s t1) (submsg_msg' t' s t2) 
                           end
            |k t1 => match t' with 
                       | k t2 => if (check_eq_msg t1 t2) then s else ( k (submsg_msg' t' s t1))
                       | _ =>  k (submsg_msg' t' s t1)
                     end
            | nc t1 =>  match t' with
                         | nc t2 => if (check_eq_msg t1 t2) then s else ( nc  (submsg_msg' t' s t1) )
                         | _ =>  nc  (submsg_msg' t' s t1) 
                       end
            | to t1 => match t' with
                         | to t2 => if (check_eq_msg t1 t2) then s else ( to  (submsg_msg' t' s t1) )
                         | _ =>  to  (submsg_msg' t' s t1) 
                       end
            | reveal t1 => match t' with
                             | reveal t2 => if (check_eq_msg t1 t2) then s else (reveal (submsg_msg' t' s t1))
                             | _  => reveal (submsg_msg' t' s t1) 
                           end
            | sign t1 t2 => match t' with 
                              | sign t3 t4 =>  if (andb (check_eq_msg t1 t3) (check_eq_msg t2 t4)) then s else (sign (submsg_msg' t' s t1) (submsg_msg' t' s t2))
                              | _ =>  sign (submsg_msg' t' s t1) (submsg_msg' t' s t2) 
                            end
            | i n' => match t' with 
                        | i n'' => if (beq_nat n' n'') then s else (i n') 
                        | _ => i n'
                      end
            | f l =>   match t' with 
                        | f l' => if (@check_eq_listm (check_eq_msg) l l') then s else (f (@map message message  (submsg_msg' t' s) l))
                        | _ => (f (@map message message  (submsg_msg' t' s) l))
         end            end 
      end.
       


Eval compute in (submsg_msg'  (f [ O ; O]) O   (if_then_else_M (EQ_M (f [ O ; O]) O) O O)).




(****************check for constant term ***********************************************************************)
Definition const_bol (t:Bool) : bool :=
 match t with 
| Bvar n' => false
| FAlse => true
| TRue => true
| EQ_B  b1 b2 =>  false
| EQ_M t1 t2 => false
| if_then_else_B t1 t2 t3 => false
| EQL t1 t2 => false
| ver t1 t2 t3 => false
end.

Definition const_msg (t:message) : bool :=
 match t with 
| if_then_else_M b3 t1 t2 => false
| (Mvar n') => false
| O => true
| lnc => true
| lsk => true
| acc => true
| N n'=> false
| new => true
| exp t1 t2 t3 => false
| pair t1 t2 => false
| pi1 t1 => false
| pi2 t1 => false
| ggen t1 => false
| act t1 => false
| rr t1 => false
| rs t1 => false
| L t1 => false
| m t1 => false
| enc t1 t2 t3 =>  false
| dec t1 t2 => false
| k t1 => false
| nc t1 => false
| to t1 => false
| reveal t1 => false
| sign t1 t2 => false
| i n' => true
| f  l => false

end.

 
Eval compute in pair( O, O).