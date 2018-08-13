(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                   University of Missouri-Columbia.                   *)
(*                                                                      *)
(*                                                                      *)
(*                                                                      *)
(************************************************************************)


(** * Definitions *)

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



(** Mutually dependent inductive types: [Bool] and [message] 
Note that type [Bool] is different from the built-in type [bool]
 *)  


Set Boolean Equality Schemes. 
Set Decidable Equality Schemes.
 
Inductive message : Type :=
| Mvar : nat -> message
| O: message
| acc : message
| lsk : message
| lnc : message
| N: nat -> message
| ifm: Bool -> message -> message -> message
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
| eqb : Bool -> Bool -> Bool
| eqm : message -> message -> Bool
| ifb :  Bool -> Bool -> Bool -> Bool
| EQL : message -> message -> Bool
| ver : message -> message -> message -> Bool.

(*
Scheme message_ind := Induction for message Sort Prop
                      with Bool_ind := Induction for Bool Sort Prop.
Combined Scheme mb_ind from message_ind, Bool_ind.
*)
(** Polymorphic length-indexed list *) 

Inductive ilist (A:Type) : nat -> Type :=
| Nil : ilist A 0
| Cons: forall n, A-> ilist A n  -> ilist A (S n).

(** Notations *)
 
Notation "x :: l" := (Cons _ _ x l )(at level 60, right associativity).
Notation "[]" := (Nil _) (at level 1).
Notation "[ x ; .. ; y ]" := (Cons _ _ x ..(Cons _ _ y (Nil _)) ..) .

(** [oursum] *)

Inductive oursum : Type:= 
| msg :  message -> oursum
| bol :  Bool  -> oursum.
 
 
(** [mylist]: an [ilist] with type [oursum] *)

Definition mylist : nat-> Type := ilist oursum.
 (** [notb] *)

Definition  notb (b: Bool) := (ifb b (FAlse) (TRue)).

(* if_then is defined
Definition if_then (b:Bool) (t:message) := ifm b t O.*)

(** [andB] *)
Definition andB (b1 b2 :Bool) := ifb b1 b2 FAlse.
Notation " b1 & b2" := (andB b1 b2 ) (at level 0).

(** [orB] *)

Definition orB (b1 b2 : Bool) := (ifb (notb b1) (ifb b2 TRue FAlse) TRue).
 (*Notation "b1 | b2" := (orB b1 b2) (at level 0).*)


(** [ggen] is randomized algorithm takes name and outputs a pair, group descriptor and generator *)
(** Group descriptor [G]: proj1 of the pair *)
Definition G (n: nat) := (pi1 (ggen (N n))).

(** Group generator [g]: proj2 of the pair *)
Definition g( n:nat) := (pi2 (ggen (N n))).

(** [k] acts as key generation algorithm that take agent name and output a [pair] of public and private keys *)

Definition pk (n:nat) := (pi1 (k (N n))).
Definition sk (n:nat) := (pi2 (k (N n))).

(** [rr] represents randomness *)
Definition r (n:nat) := (rr (N n)). 

(** Check if a term of oursum starts with [bol] constructor *)

Definition chkbol_os (a : oursum) : bool  :=
match a with
| bol a' => true
| msg a'=> false
end.

(** Check if a term of [oursum] starts with [msg] constructor *)

Definition chkmsg_os (a : oursum) : bool  :=
match a with
| bol a' => false
| msg a' => true
end.

(** Get [Bool] term out of an [oursum] term *)

Definition ostobol (a :oursum) : Bool :=
 match a with
| bol a' => a'
| msg a' => TRue
end. 

(** Get [msg] term out of an [oursum] term *)
          
Definition ostomsg (a : oursum) : message :=
match a with
| bol a' => O
| msg a' => a'
end.


(** [ilist message n] --> [mylist n] *)

Fixpoint conv_mlist_mylist {n:nat} (ml : ilist message n) : mylist n :=

match ml with
| Nil => []
| a :: h => msg a :: (conv_mlist_mylist h)
end.

(** [ilist Bool n] --> [mylist n] *)


Fixpoint conv_blist_mylist {n:nat} (ml : ilist Bool n) : mylist n :=
match ml with
| Nil => []
| a :: h => bol a :: (conv_blist_mylist h)
end.

(** [list message] --> [mylist (length l)] *)

Fixpoint conv_listm_mylist ( l :  list message) : mylist (length l) :=
match l with
| nil => []
| cons a h => msg a :: (conv_listm_mylist h)
end.

(** [mylist n] --> [list messge] *)

Fixpoint conv_mylist_listm {n:nat} (osl: mylist n) : list message :=
match osl with
| [] => nil
| a :: h => cons  (if (chkmsg_os a) then (ostomsg a) else O) (conv_mylist_listm h)
 
end.

(** [mylist n] --> [list oursum] *)

Fixpoint conv_mylist_listos {n:nat} (osl:mylist n) :list oursum :=
match osl with 
| [] => nil
| a :: h => (cons a (conv_mylist_listos h ) )
end.

(** [mylist n] --> [ilist Bool n] *)

Fixpoint conv_mylist_listb {n:nat} (osl: mylist n) : ilist Bool n :=
match osl with
| [] => @Nil Bool
| a :: h => Cons _ _ (if (chkbol_os a) then (ostobol a) else TRue) (conv_mylist_listb h)
end.

(** [list oursum] --> [mylist (length l)] *)

Fixpoint conv_listos_mylist (l : list oursum) : (mylist (length l)) :=
match l with
| nil => []
| cons h t => h:: (conv_listos_mylist t)
end.

(** [Sublist] *)

Definition sublist {A:Type} (n m:nat) (l:list A) :=
  skipn n (firstn m l).
 
(** Substitution: x <- s in t, where x, s, and t are [Bool] or [message] *)

Reserved Notation "'[[' x ':=' s ']]' t" (at level 0).
Reserved Notation "'{{' x ':=' s '}}' t" (at level 0).

Fixpoint submsg_bol (n : nat )(s:message) (b:Bool) : Bool :=
  match b with
    | eqb  b1 b2 =>  eqb  ([[n:= s]]b1) ([[n:= s]] b2)
    | eqm t1 t2 => eqm ( {{n:= s }} t1) ( {{ n:=s }} t2)
    | ifb t1 t2 t3 => ifb  ([[n:=s]]t1) ( [[n:=s]] t2) ( [[n:=s]]t3) 
    | EQL t1 t2 => EQL ( {{ n := s }} t1) ( {{ n:=s }} t2)
    | ver t1 t2 t3 => ver ({{n:=s}}t1) ({{n:=s}}t2) ({{n:=s}}t3)
       | _ => b
  end
    where "'[[' x ':=' s ']]' t" := (submsg_bol x s t)
with submsg_msg (n : nat )(s:message) (t:message) : message :=
       match t with 
         | ifm b3 t1 t2 => ifm ([[n:=s]] b3) ({{n:=s}} t1) ({{n:=s}} t2)
         | (Mvar n') =>  if (beq_nat n' n) then s else t
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
         | reveal t1 => reveal ( {{ n:=s }} t1)
         | sign t1 t2 => sign ({{n:=s}}t1) ({{n:=s}}t2)
         | f l =>  (f (@map message message  (submsg_msg n s) l))
         | _ => t
       end
         where "'{{' x ':=' s '}}' t" := (submsg_msg x s t).

(** Substitution: x <- s in t, x is of type variable, t is of [oursum] *)

Definition submsg_os (n:nat)(s:message) (t:oursum):oursum :=
match t with 
| msg t1 =>  msg ({{n := s}} t1)
| bol b1 =>  bol ( [[n := s]] b1)
end.

(** Substitution in [ilist message n'] *)

Fixpoint submsg_mlist  {n' :nat} (n:nat)(s:message)(l : ilist message n') : ilist message n' :=
match l with 
| [] => []
| h::t  =>  ({{n := s}} h) :: (submsg_mlist n s t )
end.
Eval compute in (submsg_msg 1 O  (f [ (Mvar 1) ; (N 2) ; (N 1)])).
Eval compute in  ( {{ 1 := O }} (N 1) ).


(** Substitutions for [Bool] variable in [Bool] and [message] *)

Reserved Notation "'[' x ':=' s ']' t" (at level 0).
Reserved Notation "'(' x ':=' s ')' t" (at level 0).
 
Fixpoint subbol_bol (n : nat )(s:Bool) (b:Bool) : Bool :=
  match b with 
    | Bvar n' =>  if (beq_nat n' n) then s else b
    | eqb  b1 b2 =>  eqb  ([n:=s] b1) ([n:=s] b2)
    | eqm t1 t2 => eqm ((n:= s)t1) ((n:=s) t2)
    | ifb t1 t2 t3 => ifb  ([n:=s] t1) ([n:=s] t2) ([n:=s] t3)
    | EQL t1 t2 => EQL ((n:=s) t1) ((n:=s) t2)
    | ver t1 t2 t3 => ver ((n:=s)t1) ((n:=s)t2) ((n:=s)t3)
    | _ => b
   end
    where "'[' x ':=' s ']' t" := (subbol_bol x s t)
with subbol_msg (n : nat )(s:Bool) (t:message) : message :=
       match t with 
         | ifm b3 t1 t2 => ifm ([n:=s] b3) ((n:=s)t1) ( (n:=s)t2)
         | exp t1 t2 t3 => exp (( n:=s ) t1) (( n:=s) t2) (( n:=s ) t3)
         | pair t1 t2 => pair (( n:=s ) t1) (( n:=s) t2)
         | pi1 t1 => pi1 (( n:=s ) t1) 
         | pi2 t1 => pi2 (( n:=s ) t1) 
         | ggen t1 => ggen (( n:=s ) t1)
         | act t1 => act(( n:=s ) t1)
         | rr t1 => rr ((n:=s) t1)
         | rs t1 => rs ((n:=s) t1)
         | L t1 => L ((n:=s) t1)
         | m t1 => m (( n:=s ) t1)
         | enc t1 t2 t3 => enc (( n:=s ) t1) (( n:=s) t2) (( n:=s ) t3)
         | dec t1 t2 => dec  (( n:=s ) t1) (( n:=s) t2) 
         | k t1 => k (( n:=s ) t1)
         | nc t1 =>  nc (( n:=s ) t1)
         | to t1 => to (( n:=s ) t1)
         | reveal t1 => reveal (( n:=s ) t1)
         | sign t1 t2 => sign ((n:=s)t1) ((n:=s)t2)
         | f l => (f (@map message message (subbol_msg n s) l))
         | _ => t
       end
         where "'(' x ':=' s ')' t" := (subbol_msg x s t).

(** Substitution for [Bool] variable in a term of type [oursum] *)

Definition  subbol_os (n:nat)(s:Bool) (t:oursum):oursum :=
  match t with 
    |msg t1 =>  msg ((n := s) t1)
    |bol b1 =>  bol ( [n := s] b1)
  end.

(** Testing properties on list elements*)

Fixpoint test_list {X:Type} (test: X -> bool) (l:list X): bool := 
  match l with
    | nil => true
    | cons h t => if (test h) then (test_list test t) else false
  end.
  
(** Check if a term is ground *)

Fixpoint clos_bol (b :Bool):bool:=
  match b with 
    | Bvar n' =>  false
    | eqb  b1 b2 =>  (andb (clos_bol b1) (clos_bol b2))
    | eqm t1 t2 => (andb (clos_msg t1) (clos_msg t2))
    | ifb b t1 t2 =>  andb (clos_bol b) (andb (clos_bol t1) (clos_bol t2))
    | EQL t1 t2 => (andb (clos_msg t1) (clos_msg t2))
    | ver t1 t2 t3 => (andb (andb (clos_msg t1) (clos_msg t2)) (clos_msg t3))
    | _ => true                     
  end
with clos_msg (t:message) : bool:=
       match t with 
         | ifm b t1 t2 => andb (clos_bol b) (andb (clos_msg t1) (clos_msg t2))
         | (Mvar n') => false
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
         | f l => (@forallb message clos_msg l) 
         | _ => true
       end.


(** Check if a term of type of [oursum] is closed *)

Definition clos_os (t:oursum): bool :=
  match t with 
    | msg t1 =>  clos_msg (t1)
    | bol b1 =>  clos_bol (b1)
  end. 

(** Check if every element of [message] list is closed *)

Fixpoint clos_listm (l: list message):bool:=
  match l with 
    | nil=> true
    | cons  h t => (andb (clos_msg h) (clos_listm t))
  end.

(** Check if every element of [Bool] list is closed *)

Fixpoint clos_listb (l: list Bool ):bool:=
  match l with 
    | nil=> true
    | cons h t => (andb (clos_bol h) (clos_listb t))
  end.

(** Check if [mylist] is closed *)

Fixpoint clos_mylist {n:nat} (l: mylist n):bool :=
  match l with 
    | Nil => true
    | h :: t => (andb (clos_os h) (clos_mylist t))
  end.

(** Check if a variable occure in a term of type [message] or [Bool] *)

Fixpoint var_free_bol (n : nat )(t:Bool) : bool :=
  match t with 
    | Bvar n' => if (beq_nat n' n) then true else false
    | eqb  b1 b2 =>  orb (var_free_bol n b1)  ( var_free_bol n b2)
    | eqm t1 t2 => orb (var_free_msg n t1) ( var_free_msg n t2)
    | ifb t1 t2 t3 => orb ( var_free_bol n t1)  (orb (var_free_bol n t2)(var_free_bol n t3) )
    | EQL t1 t2 => orb ( var_free_msg n t1) ( var_free_msg n t2)
    | ver t1 t2 t3 => (orb  (orb (var_free_msg n t1) (var_free_msg n t2)) (var_free_msg n t3))
    | _ => true
  end
with var_free_msg (n : nat )(t:message) : bool :=
       match t with 
         | ifm b3 t1 t2 => orb (var_free_bol n b3) (orb ( var_free_msg n  t1)( var_free_msg n t2))
         | (Mvar n') => if (beq_nat n' n) then true else false
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
         | f l => (@forallb message (var_free_msg n) l)
         | _ => true
       end.            


(** Check if a variable occur in a term of type [oursum] *)

Definition var_free_os (n:nat) (t:oursum) : bool :=
  match t with
    | msg t1 => (var_free_msg n t1)
    | bol b1 => (var_free_bol n b1)
  end.

(** Check if [mylist] contain a variable in one of the element *)

Fixpoint var_free_mylist (n:nat) {m} (l:mylist m) : bool :=
  match l with
    | [] => false
    | h :: t => (orb (var_free_os n h) (var_free_mylist n t))
  end.

(** Concatenation of two mylists *)

Fixpoint app_mylist {n1} {n2}  (ml1 : mylist n1) (ml2 : mylist n2) : mylist (plus n1 n2) :=
  match ml1 in (ilist _ n1) return (ilist _ (n1 + n2)) with
    | [] => ml2
    | Cons n1 x ml3 => Cons _ _ x (app_mylist ml3  ml2 )
  end.
Notation "ml1 ++ ml2 " := (app_mylist  ml1 ml2) (at level 60, right associativity).

Eval compute in message_beq (Mvar 2) (Mvar 3).
 
(** Check for absence of a variable *)

Fixpoint notoccur_bol (n : nat )(t:Bool) : bool :=
  match t with 
    | eqb  b1 b2 =>  andb (notoccur_bol n b1)  (notoccur_bol n b2)
    | eqm t1 t2 => andb (notoccur_msg n t1) ( notoccur_msg n t2)
    | ifb t1 t2 t3 => andb ( notoccur_bol n t1)  (andb (notoccur_bol n t2)(notoccur_bol n t3) )
    | EQL t1 t2 => andb ( notoccur_msg n t1) ( notoccur_msg n t2)
    | ver t1 t2 t3 => (andb  (andb (notoccur_msg n t1) (notoccur_msg n t2)) (notoccur_msg n t3))
    | _ => true                     
  end
with notoccur_msg (n : nat )(t:message) : bool :=
       match t with 
         | ifm b3 t1 t2 => andb (notoccur_bol n b3) (andb ( notoccur_msg n  t1)( notoccur_msg n t2))
         | N n'=> if (beq_nat n' n) then false else true
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
         | f l => (@forallb message (notoccur_msg n) l) 
         | _ => true               
       end.            
Eval compute in (notoccur_msg 1 (pi2 (N 2))).

(** Check if absence of a variable in a term of [oursum] *)

Definition  notoccur_os (n:nat)(t:oursum): bool :=
  match t with 
  | bol b => notoccur_bol n b 
  | msg t => notoccur_msg n t
  end.

(** Check if absence of a variable in [ilist] *)

Fixpoint notoccur_mlist (x:nat) {n} (ml : ilist message n):bool :=
  match ml with
    | [] => true
    | h:: ml1 => (andb (notoccur_msg x h) (notoccur_mlist x ml1))
  end.

(** Check if absence of a variable in [ilist] *)

Fixpoint notoccur_blist {m:nat}(x:nat) (ml : ilist Bool m):bool :=
  match ml with
    | [] => true
    | h :: ml1 => (andb (notoccur_bol x h) (notoccur_blist x ml1))
  end.

(** Check if absence of a variable in [mylist] *)

Fixpoint notoccur_mylist {m:nat}(x:nat) (ml :  mylist m):bool :=
  match ml with
    | [] => true
    | h :: ml1 => (andb (notoccur_os x h) (notoccur_mylist x ml1))
  end.

(** Number of occurences of an element in [ilist] *)

Fixpoint count_occur {n:nat} (x : nat)(l : ilist nat n) : nat :=
  match l with
    | [] => 0
    | y::t =>  if (beq_nat y x) then S (count_occur x t) else (count_occur x t)
  end.
Eval compute in (count_occur 1 [1;1;1]).

(** Check if no redundancies in [ilist] *)

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

(** Check if each element in [ilist nat n] occurs in [ilist message m] *)

Fixpoint notocclist_mlist {n:nat} (nl:ilist nat n){m}(ml:ilist message m): bool :=
  match nl with
    | [] => true
    | h::t=> (andb (notoccur_mlist h ml) (notocclist_mlist t ml))
  end.

Eval compute in (notoccur_mlist 1 [(N 2);(N 4)]).
Eval compute in True \/ False.

(** Check if each element in (ilist nat n) occurs in (mylist m) *)

Fixpoint notocclist_mylist {n:nat} {m:nat}(nl:ilist nat n)(ml: mylist m): bool :=
match nl with
|[] => true
| h::t=> (andb (notoccur_mylist h ml) (notocclist_mylist t ml))
end.
Eval compute in (notoccur_mylist 1 [msg (N 2); msg (N 4)]).

(** Check if an element occurs in [ilist] *)

 Fixpoint notoccur_nlist {n:nat}(a:nat) (l:ilist nat n) : bool :=
    match l with
      | Nil => true
      | h::t =>   if (beq_nat h a) then false else (andb true (notoccur_nlist a t) )
    end.
Eval compute in (notoccur_nlist 1 [2;3;1]).
Eval compute in (S (pred 1)).

(** Function [Fresh] to check if the list of numbers are freshly generated numbers *)

Definition Fresh {n:nat}{m:nat} (nl : ilist nat n)(ml : mylist m): bool :=
  match nl with 
    | [] => true
    | [a] => (notoccur_mylist a ml) 
    | l => (andb (nodup_ilist l) (notocclist_mylist l ml) )
  end. 

(** Check if an [exp term (exp (G n) (g n) (r n1))] occurs in a term *)
(** Check if a term t of type message occurs in a term of either [message] or [Bool] type *)

Fixpoint checkmtbol (t:message) (b:Bool) : bool :=
  match b with 
    | eqb  b1 b2 =>  orb (checkmtbol t b1)  (checkmtbol t b2)
    | eqm t1 t2 => orb (checkmtmsg t t1) ( checkmtmsg t t2)
    | ifb t1 t2 t3 => orb ( checkmtbol t t1)  (orb (checkmtbol t t2)(checkmtbol t t3) )
    | EQL t1 t2 => orb ( checkmtmsg t t1) ( checkmtmsg t t2)
    | ver t1 t2 t3 => (orb  (orb (checkmtmsg t t1) (checkmtmsg t t2)) (checkmtmsg t t3))
    | _ => false
  end
with checkmtmsg (t:message) (t':message) : bool :=
       if (message_beq t t') then true else
         match t' with
           | ifm b3 t1 t2 => orb (checkmtbol t b3) (orb ( checkmtmsg t  t1)( checkmtmsg t t2))
           | exp t1 t2 t3 =>  (orb (checkmtmsg t t1) (orb (checkmtmsg t t2) (checkmtmsg t t3)))
           | pair t1 t2 => orb( checkmtmsg t t1) ( checkmtmsg t t2)
           | pi1 t1 => ( checkmtmsg t t1)
           | pi2 t1 => ( checkmtmsg t t1)
           | ggen t1 => ( checkmtmsg t t1)
           | act t1 => ( checkmtmsg t t1)
           | rr t1 => ( checkmtmsg t t1)
           | rs t1 => (checkmtmsg t t1)
           | L t1 => (checkmtmsg t t1)
           | m t1 => ( checkmtmsg t t1)
           | enc t1 t2 t3 =>  orb ( checkmtmsg t t1) (orb ( checkmtmsg t t2) ( checkmtmsg t t3))
           | dec t1 t2 => orb( checkmtmsg t t1) ( checkmtmsg t t2)
           | k t1 => ( checkmtmsg t t1)
           | nc t1 =>( checkmtmsg t t1)
           | to t1 => (checkmtmsg t t1) 
           | reveal t1 => (checkmtmsg t t1)
           | sign t1 t2 => (orb (checkmtmsg t t1) (checkmtmsg t t2))
           | f l => (@existsb message (checkmtmsg t) l)
                           
           | _ => false
         end.            
          
 

(** Check for given term [(exp (G n) (g n) (r n1))] occurs in [oursum] *)
(** Check if a message term occurs in a term of [oursum] *)

Definition checkmtos (t:message) (t':oursum): bool :=
  match t' with 
    |bol b => checkmtbol t b 
    |msg t'' => checkmtmsg t t''
  end.


(** Check for [exp] term in a term of type [list message] *)

Fixpoint checkmtlism (t:message) (l: list message):bool :=
  match l with
    | nil => false
    |  cons h t' => (orb (checkmtmsg t h) (checkmtlism t t'))
  end.

(** Check for [exp] term in a term of type [mylist] *)

Fixpoint checkmtmylis (t:message) {m} (l: mylist m):bool :=
  match l with
    | [] => false
    |  h::t' => (orb (checkmtos t h) (checkmtmylis t t'))
  end.

(** Get an element at a [pos] in [mylist] *)

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

        
(** Get an element at a [pos] in [ilist] *)

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

(** Appending an element to [mylist] at front *)

Fixpoint app_elt_front (x:oursum) {n} (ml: mylist n) : mylist ( S n):=
  match ml with
    | [] => [x]
    | ml3 => (app_mylist [x] ml3)
  end.
Notation " x +++ m1 " := (app_elt_front x m1)(at level 0, right associativity).
Eval compute in getelt_at_pos  2 [bol (Bvar 1) ; bol (Bvar 2); msg (N 1); msg (N 2); msg (N 3)].


(** Appending an element of [mylist] at rear *)

Fixpoint app_elt_last (x:oursum) {n} (ml: mylist n) : mylist ( S n):=
  match ml with
    | [] => [x]
    | h::ml3 => h :: (app_elt_last x ml3)
  end.

(** Reversing [mylist] *)

Fixpoint reverse {n}(ml: mylist n) : mylist n :=
  match ml with
    | [] => []
    | x :: ml' => (app_elt_last x (reverse ml') )
  end.

(** Insert an element at given position *)

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

(** Check if the term at [pos] is [Bool] *)

Definition chkbol_at_pos  {m} (n :nat) (ml :mylist m) : bool := (chkbol_os (getelt_at_pos  n ml)).

(** Check if the term at [pos] is [message] *) 

Definition chkmsg_at_pos {m} (n :nat) (ml :mylist m) : bool := (chkmsg_os (getelt_at_pos n ml)).


(** Negating an element at given [pos] in [mylist] *)

Definition neg_at_pos {m}   (p:nat ) (ml : mylist m) : mylist 1 :=
match  (chkbol_os (getelt_at_pos p ml)) with
| true => [bol (notb (ostobol (getelt_at_pos p ml)))]
| false =>  [(getelt_at_pos p ml)]
end .

Eval compute in neg_at_pos  2  [bol (Bvar 1) ; bol (Bvar 2); msg (N 1); msg (N 2); msg (N 3)].

(** Pairing two elements from [mylist] *)

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


(** Constructing [exp] term with three terms at positions p1, p2, and p3 in [mylist] *)

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

(** Constructing a [eqm] term in with the elements in [mylist] *)

Definition eqm_at_pos {m}  (p1 p2 : nat) (ml : mylist m) : Bool :=
  match (chkmsg_os (getelt_at_pos  p1 ml)) with
    | true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
                | true => (eqm (ostomsg (getelt_at_pos  p1 ml)) (ostomsg (getelt_at_pos  p2 ml)))
                | false => (eqm (ostomsg (getelt_at_pos  p2 ml)) O)
              end
    | false => match (chkmsg_os (getelt_at_pos p2 ml)) with
                 | true => (eqm O (ostomsg (getelt_at_pos  p2 ml)))
                 | false => (eqm O O)
               end
  end.

(** Constructing a [eqb] term in with the elements in [mylist] *)

Definition eqb_at_pos {m}(p1 p2 : nat) (ml : mylist m) : Bool :=
  match (chkbol_os (getelt_at_pos  p1 ml)) with
    | true => match (chkbol_os (getelt_at_pos  p2 ml)) with
                | true => (eqb (ostobol (getelt_at_pos  p1 ml)) (ostobol (getelt_at_pos  p2 ml)))
                | false => (eqb (ostobol (getelt_at_pos  p1 ml)) TRue)
              end
    | false => match (chkbol_os (getelt_at_pos  p2 ml)) with
                 | true => (eqb TRue (ostobol (getelt_at_pos  p2 ml)))
                 | false => (eqb TRue TRue)
               end
  end.

(** Constructing a [andB] term in with the elements in [mylist] *)

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

(** Negating an element at [pos] in [mylist] *)

Definition notB_at_pos {m} (p : nat) (ml : mylist m) : Bool :=
  match (chkbol_os (getelt_at_pos  p ml)) with
    | true =>  notb (ostobol (getelt_at_pos  p ml))    
    | false => notb (TRue)
  end.


(** Construction [ifm] term from [mylist] *)

Definition IfM_at_pos {m}  (p1 p2 p3 p4 :nat)(ml : mylist m) : message :=
  match (chkbol_os (getelt_at_pos  p1 ml)) with 
    | true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
                | true => match (chkmsg_os (getelt_at_pos  p3 ml)) with
                            | true =>  (ifm (ostobol (getelt_at_pos  p1 ml)) (ostomsg (getelt_at_pos  p2 ml))  ((ostomsg (getelt_at_pos  p3 ml))))
                            | false => (ifm (ostobol (getelt_at_pos  p1 ml)) (ostomsg (getelt_at_pos  p2 ml)) O)
                          end
                | false =>  match (chkmsg_os (getelt_at_pos  p3 ml)) with
                              | true =>  (ifm (ostobol (getelt_at_pos  p1 ml)) O ((ostomsg (getelt_at_pos  p3 ml))))
                              | false => (ifm (ostobol (getelt_at_pos  p1 ml)) O  O)
                            end
              end
    | false =>  match (chkmsg_os (getelt_at_pos  p2 ml)) with
                  | true => match (chkmsg_os (getelt_at_pos  p3 ml)) with
                              | true =>  (ifm TRue (ostomsg (getelt_at_pos  p2 ml))  ((ostomsg (getelt_at_pos  p3 ml))))
                              | false => (ifm TRue (ostomsg (getelt_at_pos  p2 ml)) O)
                            end
                  | false =>  match (chkmsg_os (getelt_at_pos  p3 ml)) with
                                | true =>  (ifm TRue O ((ostomsg (getelt_at_pos  p3 ml))))
                                | false => (ifm TRue O  O)
                              end
                end
                  
  end.

(** Construction [ifb] with terms in [mylist] *)

Definition IfB_at_pos {m}  (p1 p2 p3 p4 :nat)(ml : mylist m) : Bool :=
  match (chkbol_os (getelt_at_pos  p1 ml)) with 
    | true => match (chkbol_os (getelt_at_pos  p2 ml)) with
                | true => match (chkbol_os (getelt_at_pos  p3 ml)) with
                            | true =>  (ifb (ostobol (getelt_at_pos  p1 ml)) (ostobol (getelt_at_pos  p2 ml))  ((ostobol (getelt_at_pos  p3 ml))))
                            | false => (ifb (ostobol (getelt_at_pos  p1 ml)) (ostobol (getelt_at_pos  p2 ml)) TRue)
                          end
                | false =>  match (chkbol_os (getelt_at_pos  p3 ml)) with
                              | true =>  (ifb (ostobol (getelt_at_pos  p1 ml)) TRue ((ostobol (getelt_at_pos  p3 ml))))
                              | false => (ifb (ostobol (getelt_at_pos  p1 ml)) TRue  TRue)
                            end
              end
    | false =>  match (chkbol_os (getelt_at_pos  p2 ml)) with
                  | true => match (chkbol_os (getelt_at_pos  p3 ml)) with
                              | true =>  (ifb TRue (ostobol (getelt_at_pos  p2 ml))  ((ostobol (getelt_at_pos  p3 ml))))
                              | false => (ifb TRue (ostobol (getelt_at_pos  p2 ml)) TRue)
                            end
                  | false =>  match (chkbol_os (getelt_at_pos  p3 ml)) with
                                | true =>  (ifb TRue TRue ((ostobol (getelt_at_pos  p3 ml))))
                                | false => (ifb TRue TRue TRue)
                              end
                end
                  
  end.

(** Constructing a [pair] term from [mylist] *)

Definition pair_term_pos {n}  (m:message) (p:nat)  (ml : mylist n): message :=
  (pair m (ostomsg (getelt_at_pos  p ml))).

(** [If_then_else_M] b1 m1 ( ( m1, m2), m3) : b1 at n1, m1 at n2, m2 at n3, m3 at n4 *)

Definition ifm_nespair {m}  (p1 p2 p3 p4 :nat)(ml : mylist m) : message := 
  match (chkbol_os (getelt_at_pos  p1 ml)) with 
    | true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
                | true => ifm  (ostobol (getelt_at_pos  p1 ml)) (ostomsg (getelt_at_pos  p2 ml))  (pair_term_pos  (pair_at_pos  p2 p3 ml) p4 ml)
                | false => (ifm  (ostobol (getelt_at_pos  p1 ml)) O (pair_term_pos  (pair_term_pos  O p3 ml) p4 ml))
              end
    |false => match (chkmsg_os (getelt_at_pos  p2 ml)) with
                | true => (ifm  TRue (ostomsg (getelt_at_pos  p2 ml))  (pair_term_pos  (pair_at_pos  p2 p3 ml) p4 ml))
                | false => (ifm  TRue  O (pair_term_pos  (pair_term_pos  O p3 ml)  p4 ml))
              end
  end.

Eval compute in ifm_nespair  1 3 4 5  [bol (Bvar 1) ; bol (Bvar 2); msg (N 1); msg (N 2); msg (N 3)].


(** [If_then_else_M] b1 m1 (m2, m3) : b1 at n1, m1 at n2, m2 at n3, m3 at n4 *)

Definition ifm_pair {m}  (p1 p2 p3 p4 :nat)(ml : mylist m) : message := 
  match (chkbol_os (getelt_at_pos  p1 ml)) with 
    | true => match (chkmsg_os (getelt_at_pos  p2 ml)) with
                | true => (ifm  (ostobol (getelt_at_pos  p1 ml)) (ostomsg (getelt_at_pos  p2 ml)) (pair_at_pos  p3 p4 ml))
                | false => (ifm  (ostobol (getelt_at_pos  p1 ml)) O  (pair_at_pos  p3 p4 ml))
              end
    |false => match (chkmsg_os (getelt_at_pos  p2 ml)) with
                | true => (ifm  TRue (ostomsg (getelt_at_pos  p2 ml))  (pair_at_pos  p3 p4 ml))
                | false => (ifm  TRue  O  (pair_at_pos  p3 p4 ml))
              end
  end.
            
Eval compute in ifm_pair 1 2 3 4  [bol (Bvar 1) ; bol (Bvar 2); msg (N 1); msg (N 2); msg (N 3)].
  
(** Dropping the last element in [mylist] *)

Definition dropone {n:nat} (m:mylist n):(mylist (pred n)):=
  match m with 
    | [] => []
    |  h:: m1 => m1
  end.

(** Dropping last two elements in a [mylist] *)

Definition  droptwo {n:nat} (ml: mylist n): mylist (pred (pred n)):= (dropone (dropone ml)).

(** Apply reveal at position in [mylist] *)

Definition reveal_at_pos{m} (p:nat) (ml: mylist m) : message :=
  match (chkmsg_os (getelt_at_pos  p ml)) with
    | true =>  reveal (ostomsg (getelt_at_pos p ml) )
    | false => reveal O
  end.

(** Apply [to] at position in [mylist] *)

Definition to_at_pos {m} (p:nat) (ml: mylist m) : message :=
  match (chkmsg_os (getelt_at_pos  p ml)) with
    | true =>  to (ostomsg (getelt_at_pos  p ml) )
    | false => to O
  end.

(** Apply [act] at position in [mylist] *)

Definition act_at_pos {m} (p:nat) (ml: mylist m) : message :=
  match (chkmsg_os (getelt_at_pos  p ml)) with
    | true =>  act (ostomsg (getelt_at_pos  p ml) )
    | false => act O
  end.

(** Apply [m] at position in [mylist] *)

Definition m_at_pos {n} (p:nat) (ml:mylist n) : message :=
  match (chkmsg_os (getelt_at_pos p ml)) with
    | true =>  m (ostomsg (getelt_at_pos p ml) )
    | false => m O
  end.
Eval compute in to_at_pos 4 [bol (Bvar 1) ; bol (Bvar 2); msg (N 1); msg (N 2); msg (N 3)]. 

(** Constant function [const] *)

Definition const {X:Type}{Y:Type}(a : X) := fun _ : Y => a.
Eval compute in (const (N 0) O ).

(** Substitute [Bool] in [mylist] *)

Fixpoint subbol_mylist {n1:nat} (n:nat)(s:Bool)(ml: mylist n1):mylist n1 :=
  match ml with 
    | Nil => []
    | h::t => (subbol_os n s h) :: (subbol_mylist n s t)
  end.

(** Substitute [message] in [mylist] *)

Fixpoint submsg_mylist {n1:nat} (n:nat)(s:message)(ml: mylist n1):mylist n1 :=
  match ml with 
    | Nil => []
    | h::t => (submsg_os n s h) :: (submsg_mylist n s t)
  end.
Eval compute in (subbol_mylist 1 TRue [msg O; msg (Mvar 1); bol (Bvar 1)]).
Eval compute in (submsg_os 1  ( O) (bol (Bvar 1))).

(** Drop last element *)

Definition drpone_last {n} (l:mylist (S n)) : mylist n :=  dropone(reverse l).

(** Project last element *)

Definition proj_one {n} (l: mylist n) : mylist 1:=
  match (reverse   l)  with
    | [] => [msg O]
    | h::t => [h]
  end.

(** Project last two *)

Definition proj_two {n} (l:mylist n) : mylist 2:=
  match (reverse l) with
    |[] => [msg O; msg O]
    | h::t::l' => [t;h]
    | h:: t => [msg O; h]
  end.

(** Drop last but one *)

Definition droplastsec {n} (l:mylist n) : mylist (pred (pred n) + pred 2) :=
  let y := (proj_two l) in
  let x := (droptwo (reverse l)) in
  let y1:= (dropone y) in 
  (app_mylist (reverse x) y1).

Eval compute in (droplastsec  [msg O; msg (Mvar 1)]).

(** Project last three *)

Definition proj_three {n} (l: mylist n) : mylist 3:=
  match (reverse l) with 
    | [] => [msg O ; msg O ; msg O]
    | h :: h1 :: h2 :: l1 => [h2 ; h1 ; h]
    | h :: h1 :: t => [ msg O; h1 ; h]
    | h :: t => [msg O ; msg O ; h]
  end.

(** Drop last but third *)

Definition droplast3rd {n} (l:mylist n) : mylist (( pred (pred (pred n) ) ) + pred 3) :=
  let y := (proj_three l) in 
  let x := (dropone (droptwo (reverse l))) in
  let y1 := (dropone y) in 
  (app_mylist (reverse x) y1).

Eval compute in (droplast3rd  [ msg (Mvar 1)]).

(** Construct [mylist n] where each element is [msg O] *)

Fixpoint app_n_elts (n:nat) :mylist n :=
  match n with
    | 0 => []
    | S n' => (app_mylist (app_elt_front (msg O) []) (app_n_elts n'))
  end.

Eval compute in app_n_elts 3.

(** Apply [pred] on [m] for [n] times *)

Fixpoint app_pred_n (n m:nat) : nat :=
  match n with 
    | 0 => m
    | S n' => (app_pred_n n' (pred m))
  end.

(** Drop [n] elements from [mylist] *)

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

(** First [n] elements of [mylist] **)

Definition Firstn (n:nat) {m} (l: mylist m) : mylist (app_pred_n (app_pred_n n  m) m) :=  reverse (drop_n_times (app_pred_n n m ) (reverse l)).

(** Skip or remove first [n] elements in [mylist] **)

Definition Skipn (n:nat) {m} (l: mylist m) : mylist (app_pred_n n m) :=  drop_n_times n l.

(** Swap two elements in a [mylist] *)

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

(** Proj an element at a given [pos] [p] in [mylist] *)

Definition proj_at_pos (p:nat) {m} (l:mylist m) : mylist (pred (app_pred_n (app_pred_n p m) m) + app_pred_n p m) :=
  let x := (Firstn p l) in
  let y := (Skipn p l) in
  let x1 := reverse (dropone (reverse x)) in
  x1 ++ y.

Eval compute in proj_at_pos 3  [ msg O; msg (Mvar 3); msg (Mvar 2); msg (Mvar 1)].

(** Check [equality] of two lists *)

Section def.
Variable A B :Type. 
Variable  f: message -> message -> bool.
(** check if two lists equal *)
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
  


(** Check occurence of a term in a term *)
 
Fixpoint checkbtbol ( b':Bool) (b:Bool) : bool :=
  if (Bool_beq b' b) then true else
  match b  with 
    | eqb  b1 b2 => (orb (checkbtbol b' b1) (checkbtbol b' b2))
    | eqm t1 t2 =>   (orb (checkbtmsg b' t1) (checkbtmsg b' t2))
    | ifb t1 t2 t3 =>  (orb (checkbtbol b' t1) (orb (checkbtbol b' t2) (checkbtbol b' t3)))
    | EQL t1 t2 =>   (orb (checkbtmsg b' t1 ) (checkbtmsg b' t2))
    | ver t1 t2 t3 =>   (orb (checkbtmsg b' t1)  (orb (checkbtmsg b' t2) (checkbtmsg b' t3)))
    | _ => false
  end
with checkbtmsg (b :Bool) (t:message) : bool :=
       match t with 
         | ifm b' t1 t2 =>   (orb (checkbtbol b b') (orb (checkbtmsg b t1) (checkbtmsg b t2)))
         | exp t1 t2 t3 => (orb (checkbtmsg b t1) (orb (checkbtmsg b t2) (checkbtmsg b t3)))
         | pair t1 t2 => (orb (checkbtmsg b t1) (checkbtmsg b t2))
         | pi1 t1 =>  (checkbtmsg b t1) 
         | pi2 t1 =>  (checkbtmsg b t1) 
         | ggen t1 =>  (checkbtmsg b t1) 
         | act t1 =>   (checkbtmsg b t1) 
         | rr t1 =>   (checkbtmsg b t1) 
         | rs t1 =>  (checkbtmsg b t1) 
         | L t1 =>   (checkbtmsg b t1) 
         | m t1 =>   (checkbtmsg b t1) 
         | enc t1 t2 t3 =>   (orb (checkbtmsg b t1) (orb (checkbtmsg b t2) (checkbtmsg b t3)))
         | dec t1 t2 => (orb (checkbtmsg b t1) (checkbtmsg b t2))
         | k t1 =>  (checkbtmsg b t1) 
         | nc t1 => (checkbtmsg b t1) 
         | to t1 =>  (checkbtmsg b t1) 
         | reveal t1 =>  (checkbtmsg b t1) 
         | sign t1 t2 =>(orb (checkbtmsg b t1) (checkbtmsg b t2))
         | _ => false
       end. 


   
(** Substitute term ts ([Bool]) for a term t'([Bool]) replace b' with s in b *)

Fixpoint subbol_bol'  (b' : Bool) (s: Bool) (b :Bool) : Bool :=
  if (Bool_beq b' b) then s else
    match b  with
      | eqb b1 b2 => eqb (subbol_bol' b' s b1) (subbol_bol' b' s b2)
      | eqm t1 t2 => eqm (subbol_msg' b' s t1) (subbol_msg' b' s t2)
      | EQL t1 t2 => EQL (subbol_msg' b' s t1) (subbol_msg' b' s t2)
      | ifb b1 b2 b3 => ifb (subbol_bol' b' s b1) (subbol_bol' b' s b2) (subbol_bol' b' s b3)
      | ver t1 t2 t3 =>  ver (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)
      | _             => b             
    end
with subbol_msg' (b' : Bool )(s: Bool) (t:message) : message :=
       match t with 
         | ifm b t1 t2 =>    (ifm (subbol_bol' b' s b) (subbol_msg' b' s t1) (subbol_msg' b' s t2))                                     
         | exp t1 t2 t3 =>   exp  (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)
         | pair t1 t2 => pair (subbol_msg' b' s t1) (subbol_msg' b' s t2)
         | pi1 t1 =>  pi1 (subbol_msg' b' s t1)
         | pi2 t1 =>  pi2 (subbol_msg' b' s t1)
         | ggen t1 =>   ggen (subbol_msg' b' s t1)
         | act t1 =>  act (subbol_msg' b' s t1)
         | rr t1 =>    rr (subbol_msg' b' s t1)
         | rs t1 =>   rs (subbol_msg' b' s t1)
         | L t1 =>  L (subbol_msg' b' s t1)
         | m t1 =>    m (subbol_msg' b' s t1)
         | enc t1 t2 t3 => enc (subbol_msg' b' s t1) (subbol_msg' b' s t2) (subbol_msg' b' s t3)
         | dec t1 t2 => dec  (subbol_msg' b' s t1) (subbol_msg' b' s t2) 
         | k t1 =>  k (subbol_msg' b' s t1)
         | nc t1 =>  nc (subbol_msg' b' s t1)
         | to t1 => to  (subbol_msg' b' s t1) 
         | reveal t1 =>  reveal (subbol_msg' b' s t1) 
         | sign t1 t2 =>   sign (subbol_msg' b' s t1) (subbol_msg' b' s t2)
         | _ => t                  
       end.
                 
     


Fixpoint submsg_bol' (t' : message)(s:message) (b:Bool) : Bool :=
  match b with
    | eqb  b1 b2 =>  (eqb (submsg_bol' t' s b1) (submsg_bol' t' s b2))
    | eqm t1 t2 => (eqm (submsg_msg' t' s t1) (submsg_msg' t' s t2))
    | ifb t1 t2 t3 => (ifb (submsg_bol' t' s t1) (submsg_bol' t' s t2) (submsg_bol' t' s t3))
    | EQL t1 t2 =>  (EQL (submsg_msg' t' s t1) (submsg_msg' t' s t2))
    | ver t1 t2 t3 => ver  (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3)
    | _ => b
  end
with submsg_msg' (t' : message )(s:message) (t:message) : message :=
if  (message_beq t' t)  then s else
  match t with 
    | ifm b1 t1 t2 => (ifm (submsg_bol' t' s b1) (submsg_msg' t' s t1) (submsg_msg' t' s t2))
    | exp t1 t2 t3 =>  exp  (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3)
    | pair t1 t2 => pair (submsg_msg' t' s t1) (submsg_msg' t' s t2)
    | pi1 t1 => pi1 (submsg_msg' t' s t1)
    | pi2 t1 => pi2 (submsg_msg' t' s t1)
    | ggen t1 =>  ggen (submsg_msg' t' s t1)
    | act t1 =>   act (submsg_msg' t' s t1)
    | rr t1 =>   rr (submsg_msg' t' s t1)
    | rs t1 =>   rs (submsg_msg' t' s t1)
    | L t1 =>  L (submsg_msg' t' s t1)
    | m t1 =>  m (submsg_msg' t' s t1)
    | enc t1 t2 t3 => enc (submsg_msg' t' s t1) (submsg_msg' t' s t2) (submsg_msg' t' s t3)
    | dec t1 t2 =>  dec  (submsg_msg' t' s t1) (submsg_msg' t' s t2) 
    | k t1 =>  k (submsg_msg' t' s t1)
    | nc t1 =>   nc  (submsg_msg' t' s t1) 
    | to t1 =>  to  (submsg_msg' t' s t1) 
    | reveal t1 => reveal (submsg_msg' t' s t1) 
    | sign t1 t2 =>  sign (submsg_msg' t' s t1) (submsg_msg' t' s t2)
    | f l =>   (f (@map message message  (submsg_msg' t' s) l))
    | _ => t
    end.
      
Eval compute in (submsg_msg' (Mvar 1) O (Mvar 2)).



(** Check if a term is constant *)

Definition const_bol (t:Bool) : bool :=
  match t with 
    | TRue => true
    | FAlse => true
    | _ => false
  end.

Definition const_msg (t:message) : bool :=
  match t with
    | O => true
    | lnc => true
    | lsk => true
    | acc => true
    | new => true
    | i _ => true
    | _ => false
  end.

(** Topsymbol equality *)

(** [message] *)

Definition topsymsg_beq (t t': message ) : bool :=
   match t, t' with
     | ifm  _ _ _ , ifm _ _ _ => true
     | ifm  _ _ _ , _ => false
     | Mvar _ , Mvar _  => true
     | Mvar _ , _  => false                            
     | exp _ _ _ , exp _ _ _ => true
     | exp _ _ _ , _ => false
     | pair _ _, pair _ _ => true
     | pair _ _,  _ => false
     | pi1 _ , pi1 _ => true
     | pi1 _ , _ => false
     | pi2 _ , pi2 _ => true
     | pi2 _ ,  _ => false
     | ggen _ , ggen _ => true
     | ggen _ ,  _ =>  false
     | act _ , act _  => true
     | act _ , _  => false
     | rr _, rr _ => true
     | rr _,  _ => false
     | rs _, rs _ => true
     | rs _, _ => false
     | L _, L _ => true
     | L _, _ => false
     | m _, m _  => true
     | m _, _  => false
     | enc _ _ _, enc _ _ _ => true
     | enc _ _ _, _ => false
     | dec _ _, dec _ _ => true
     | dec _ _, _ => false
     | k _ , k _ =>  true
     | k _ , _ =>  false
     | nc _, nc _ => true
     | nc _,  _ => false
     | to _, to _ => true
     | to _, _ => false
     | reveal _, reveal _ => true
     | reveal _, _ => false
     | sign _ _, sign _ _ =>  true
     | sign _ _, _ =>  false
     | f _ , f _ => true
     | f _ , _ => false
     | _ , _=> message_beq t t'
   end.

(** [Bool] *)

 Definition topsybol_beq (b b' : Bool) : bool :=
   match b, b' with
     | Bvar _, Bvar _ =>  true
     | eqb  _ _ , eqb _ _  =>  true
     | eqm _ _, eqm _ _ =>  true
     | ifb _ _ _, ifb _ _ _ => true
     | EQL _ _ , EQL _ _ => true
     | ver _ _ _, ver _ _ _ => true
     | Bvar _,  _ =>  false
     | eqb  _ _ , _  =>  false
     | eqm _ _,   _ =>  false
     | ifb _ _ _,  _ => false
     | EQL _ _ , _ => false
     | ver _ _ _,  _ => false
     | _ , _ => Bool_beq b b'
   end. 

 (** [oursum] *)
Definition topsyos_beq (t1 t2 : oursum): bool :=
  match t1 , t2 with
      | msg t1', msg t2' => topsymsg_beq t1' t2'
      | bol b1, bol b2 => topsybol_beq b1 b2
      | _ , _ => false
  end.

(** check if topsymbol of term occur in mylist *)
Fixpoint topsyml_beq (m:nat) (t1: message) (l:mylist m): bool :=
  match l with
    | [] => false
    | h ::t => (andb (topsymsg_beq (ostomsg h) t1) (topsyml_beq _ t1 t))
  end. 

(** check if an oursum term occurs in mylist *)
Fixpoint checkostmylis (x:oursum) {n} (l:mylist n) : bool :=
  match l with
    | [] => false
    | h :: t => if (oursum_beq x h) then true else (checkostmylis x t)
  end.

(** find an element index in mylist *)
Fixpoint eltPos  (x:oursum) {n} (l:mylist n) :nat :=
  match l with
    | [] => 0
    | h::t =>  if  (oursum_beq x h)  then 1 else S (eltPos x t)
  end.
  

(** checksublis: mylist m -> mylist n -> bool *)
Fixpoint checksublis  (l: list oursum) {n} (l':mylist n) : bool :=
match (leb n n) , l with
  | true , nil => true
  | true , cons h t => if (checkostmylis h  l') then (checksublis t l')
                     else false
  | _ , _ => false
end.

(** sublisIndcs: mylist m -> mylist n -> list nat *)
                    
 Fixpoint  sublisindcs  {n} (l :list oursum) (l': mylist n) : list nat :=
  match  l with
    | nil => nil
    | cons h t => cons (eltPos h l')  (sublisindcs t l')
  end.

(**  subterms of a term *)


Section subtrm'.
Variable f: message -> list oursum.
Fixpoint mapsubtrmls (l: list message) : list oursum :=
  match l with
    | nil => nil
    | cons h t => (app (f h) (mapsubtrmls t))
  end.
End subtrm'.

Fixpoint listmsg_os (l:list message): list oursum:=
  match l with
    |nil => nil
    | cons h t => cons (msg h) (listmsg_os t)
  end.
Definition subtrms_bol'(t: Bool) : list oursum :=
  match t with 
    | eqb  b1 b2 =>  cons (bol b1) (cons (bol b2) nil) 
    | eqm t1 t2 =>   cons (msg t1) (cons (msg t2) nil) 
    | ifb t1 t2 t3 => cons (bol t1) (cons (bol t2) (cons (bol t3) nil))
    | EQL t1 t2 =>  cons (msg t1) (cons (msg t2) nil)
    | ver t1 t2 t3 => (cons (msg t1) (cons (msg t2) (cons (msg t3) nil)))
    | _ => nil
 end.
Definition subtrms_msg' (t:message) : list oursum :=
       match t with 
         | ifm b3 t1 t2 => (cons (bol b3) (cons (msg t1) (cons (msg t2) nil))) 
         | (Mvar n') => (cons (msg (Mvar n')) nil)
         | acc => (cons (msg acc) nil)
         | lnc => (cons (msg lnc) nil)
         | lsk => (cons (msg lsk) nil)
         | O => (cons (msg O) nil)
         | N n'=> (cons (msg (N n')) nil)
         | new =>  (cons (msg new) nil)
         | exp t1 t2 t3 => (cons (msg t1) (cons (msg t2)  (cons (msg t3) nil)))
         | pair t1 t2 =>  (cons (msg  t1) (cons (msg t2) nil))
         | pi1 t1 => match t1 with
                       | k _ => (cons (msg (pi1 t1)) nil)
                       | _ => (cons (msg t1) nil)
                     end
         | pi2 t1 => match t1 with
                       | k _ => (cons (msg (pi2 t1)) nil)
                       | _ => (cons (msg t1) nil)
                     end
         | ggen t1 => cons  (msg t1) nil
         | act t1 =>  cons (msg t1) nil
         | rr t1 => cons (msg t1) nil
         | rs t1 => cons (msg t1) nil
         | L t1 => cons (msg t1) nil
         | m t1 => cons (msg t1) nil
         | enc t1 t2 t3 => (cons (msg t1) (cons (msg t2) (cons (msg t3) nil)))
         | dec t1 t2 =>  (cons (msg t1) (cons (msg t2) nil))
         | k t1 =>  cons (msg t1) nil 
         | nc n => (cons (msg (nc n)) nil) 
         | to t1 => cons (msg t1) nil
         | reveal t1 => cons (msg t1) nil
         | sign t1 t2 =>   (cons (msg t1) (cons (msg t2) nil))
         | f l => listmsg_os l
         | _ => nil
       end.


(** Subterms of [oursum] term. *)

Definition subtrms_os' (t:oursum) : list oursum :=
  match t with 
    | msg t1 => subtrms_msg' t1
    | bol b1 =>  subtrms_bol' b1
  end.

(** Subterms of terms of type [mylist n] for some [n].*)

Fixpoint subtrms_mylis' {n} (l:mylist n) : list oursum :=
  match l with 
    | [] => nil
    | h:: t => (app (subtrms_os' h) (subtrms_mylis' t))
  end.
