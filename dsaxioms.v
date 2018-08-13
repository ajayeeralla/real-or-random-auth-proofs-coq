
(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                   University of Missouri-Columbia.                   *)
(*                                                                      *)
(*                                                                      *)
(*                                                                      *)
(************************************************************************)

Load "auxthms".
             
(** This library defines the axioms _correctness_ and _existential unforgeability under chosen message attacks_. *)

(** Subterms of list of terms. *)

Section subtrm.
Variable f: message -> list message.
Fixpoint subtrmls (l: list message) : list message :=
match l with
| nil => nil
| cons h t => (app (f h) (subtrmls t))
end.
End subtrm.

(** subterms of [message], or [Bool] terms. *)

Fixpoint subtrmls_bol  (t: Bool) : list message :=
 match t with 
| Bvar n' => nil
| FAlse => nil
| TRue => nil
| eqb  b1 b2 =>  (app (subtrmls_bol  b1) (subtrmls_bol b2) )
| eqm t1 t2 => (app (subtrmls_msg t1) (subtrmls_msg t2) )
| ifb t1 t2 t3 => (app (subtrmls_bol t1) (app (subtrmls_bol t2) (subtrmls_bol t3)))
| EQL t1 t2 => (app (subtrmls_msg t1) (subtrmls_msg t2) )
| ver t1 t2 t3 =>(app (subtrmls_msg t1) (app (subtrmls_msg t2) (subtrmls_msg t3)))
 end
with subtrmls_msg (t:message) : list message :=
 match t with 
| ifm b3 t1 t2 => (app (cons (ifm b3 t1 t2) nil)  (app (subtrmls_bol b3) (app (subtrmls_msg t1) (subtrmls_msg t2))))
| (Mvar n') => (cons (Mvar n') nil)
| acc => (cons acc nil)
| lnc => (cons lnc nil)
| lsk => (cons lsk nil)
| O => (cons O nil)
| N n'=> (cons (N n') nil)
|new =>  (cons new nil)
| exp t1 t2 t3 => (app   (cons (exp t1 t2 t3) nil) (app (subtrmls_msg t1) (app (subtrmls_msg t2) (subtrmls_msg t3))))
| pair t1 t2 => (app (cons (pair t1 t2) nil) (app (subtrmls_msg  t1) (subtrmls_msg t2) ))
| pi1 t1 => (app (cons (pi1 t1) nil) (subtrmls_msg t1) )
| pi2 t1 => (app (cons (pi2 t1) nil) (subtrmls_msg t1) )
| ggen t1 => (app (cons (ggen t1) nil) (subtrmls_msg t1) )
| act t1 => (app (cons (act t1) nil) (subtrmls_msg t1) )
| rr t1 => (app  (cons (rr t1) nil) (subtrmls_msg t1) )
| rs t1 => (app (cons (rs t1) nil) (subtrmls_msg t1) )
| L t1 => (app (cons (L t1) nil)  (subtrmls_msg t1) )
| m t1 => (app ( cons (m t1) nil) (subtrmls_msg t1) )
|enc t1 t2 t3 => (app (cons (enc t1 t2 t3) nil) (app (subtrmls_msg t1) (app (subtrmls_msg t2) (subtrmls_msg t3))))
|dec t1 t2 => (app (cons ( dec t1 t2) nil) (app (subtrmls_msg t1) (subtrmls_msg t2)))
|k t1 => (app (cons (k t1) nil) (subtrmls_msg t1) )
| nc n => (cons (nc n) nil) 
| to t1 => (app (cons (to t1) nil) (subtrmls_msg t1) )
| reveal t1 => (app (cons (reveal t1) nil) (subtrmls_msg t1) )
| sign t1 t2 => (app (cons (sign t1 t2) nil)  (app (subtrmls_msg t1) (subtrmls_msg t2)))
| i n' => nil
|f  l => ((cons (f l) (@subtrmls subtrmls_msg l)))
 end.
Eval compute in (subtrmls_msg (sign (ifm TRue (dec O (sk 1)) O) new)).

(** Subterms of [oursum] term. *)

Definition subtrmls_os (t:oursum) : list message :=
match t with 
| msg t1 => subtrmls_msg t1
| bol b1 =>  subtrmls_bol b1
end.

(** Subterms of terms of type [mylist n] for some [n].*)

Fixpoint subtrmls_mylist {n} (l:mylist n) : list message :=
match l with 
| [] => nil
| h:: t => (app (subtrmls_os h) (subtrmls_mylist t))
end.
(*
(** Check if [(N n)] occurs only under either [sk] or [pk] . *)

(** [message] or [Bool]. *)
Fixpoint onlyin_pkrsk_bol (n : nat )(t:Bool) : bool :=
 match t with 
| Bvar n' => if (beq_nat n' n) then false else true
| FAlse => true
| TRue => true
| eqb  b1 b2 =>  (andb (onlyin_pkrsk_bol n b1)  (onlyin_pkrsk_bol n b2))
| eqm t1 t2 => andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2)
| ifb t1 t2 t3 =>  (andb (onlyin_pkrsk_bol n t1) (andb (onlyin_pkrsk_bol n t2) ( onlyin_pkrsk_bol n t3)))
| EQL t1 t2 =>  (andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2))
| ver t1 t2 t3 => (andb (onlyin_pkrsk_msg n t1) (andb (onlyin_pkrsk_msg n t2) ( onlyin_pkrsk_msg n t3)))
 end
with onlyin_pkrsk_msg (n : nat )(t:message) : bool :=
 match t with 
| ifm b t1 t2 => (andb (onlyin_pkrsk_bol n b) (andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2)))
| (Mvar n') =>  if (beq_nat n' n) then false else true
| O => true
| acc => true
| lsk => true
| lnc => true
| N n'=> if (beq_nat n' n) then false else true
| new =>  true
| exp t1 t2 t3 =>  (andb (onlyin_pkrsk_msg n t1) (andb (onlyin_pkrsk_msg n t2) ( onlyin_pkrsk_msg n t3)))
| pair t1 t2 =>  andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2)
| pi1 t1 => match t1 with
             | (k (N n)) => true
             | _ => true
            end
| pi2 t1 => match t1 with
             | (k (N n)) => true
             | _ => true
            end
| ggen t1 =>  (onlyin_pkrsk_msg n t1)
| act t1 =>  (onlyin_pkrsk_msg n t1)
| rr t1 =>  (onlyin_pkrsk_msg n t1)
| rs t1 =>  (onlyin_pkrsk_msg n t1)
| L t1 =>  (onlyin_pkrsk_msg n t1)
| m t1 =>  (onlyin_pkrsk_msg n t1)
| enc t1 t2 t3 =>  (andb (onlyin_pkrsk_msg n t1) (andb (onlyin_pkrsk_msg n t2) ( onlyin_pkrsk_msg n t3)))
|dec t1 t2 => andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2)
| k t1 =>  (onlyin_pkrsk_msg n t1) 
| nc t1 => (onlyin_pkrsk_msg n t1) 
| to t1 => (onlyin_pkrsk_msg n t1) 
| reveal t1 => (onlyin_pkrsk_msg n t1) 
| sign t1 t2 => andb (onlyin_pkrsk_msg n t1) ( onlyin_pkrsk_msg n t2)
| i n' => true
| f  l => (@forallb message (onlyin_pkrsk_msg n) l)
end.
Eval compute in (onlyin_pkrsk_msg 1  (f [ (k (N 1))])).

(** [oursum] *)
Definition onlyin_pkrsk_os (n : nat )(t:oursum) : bool :=
match t with
| msg t1 => (onlyin_pkrsk_msg n t1)
| bol b => (onlyin_pkrsk_bol n b)
end.

(** [mylist m] for some m *)

Fixpoint onlyin_pkrsk_mylist (n : nat ){m}(t: mylist m) : bool :=
match t with
| []  => true
| h:: tl=> (andb (onlyin_pkrsk_os n h) (onlyin_pkrsk_mylist n tl))
end.

(** Check if sk(N n) occurs as [(sign (sk (K n)) _)]. *)

Fixpoint skn_in_sign_bol (n : nat )(t:Bool) : bool :=
 match t with 
| Bvar n' =>  true
| FAlse => true
| TRue => true
| eqb  b1 b2 =>  (andb (skn_in_sign_bol n b1)  (skn_in_sign_bol n b2))
| eqm t1 t2 => andb (skn_in_sign_msg n t1) ( skn_in_sign_msg n t2)
| ifb t1 t2 t3 =>  (andb (skn_in_sign_bol n t1) (andb (skn_in_sign_bol n t2) ( skn_in_sign_bol n t3)))
| EQL t1 t2 =>  (andb (skn_in_sign_msg n t1) ( skn_in_sign_msg n t2))
| ver t1 t2 t3 => (andb (skn_in_sign_msg n t1) (andb (skn_in_sign_msg n t2) ( skn_in_sign_msg n t3)))
 end
with skn_in_sign_msg (n : nat )(t:message) : bool :=
 match t with 
| ifm b t1 t2 => (andb (skn_in_sign_bol n b) (andb (skn_in_sign_msg n t1) ( skn_in_sign_msg n t2)))
| (Mvar n') => true
| O => true
| acc => true
| lnc => true
| lsk => true
| N n'=>  true
|new =>  true
| exp t1 t2 t3 =>  (andb (skn_in_sign_msg n t1) (andb (skn_in_sign_msg n t2) ( skn_in_sign_msg n t3)))
| pair t1 t2 =>  andb (skn_in_sign_msg n t1) ( skn_in_sign_msg n t2)
| pi2 t1 => (skn_in_sign_msg n t1)
| pi1 t1 => (skn_in_sign_msg n t1)
| ggen t1 =>  (skn_in_sign_msg n t1)
| act t1 =>  (skn_in_sign_msg n t1)
| rr t1 =>  (skn_in_sign_msg n t1)
| rs t1 =>  (skn_in_sign_msg n t1)
| L t1 =>  (skn_in_sign_msg n t1)
| m t1 =>  (skn_in_sign_msg n t1)
|enc t1 t2 t3 =>  (andb (skn_in_sign_msg n t1) (andb (skn_in_sign_msg n t2) ( skn_in_sign_msg n t3)))
|dec t1 t2 => andb (skn_in_sign_msg n t1) ( skn_in_sign_msg n t2)
| k t1 =>  (skn_in_sign_msg n t1) 
| nc t1 => (skn_in_sign_msg n t1) 
 | to t1 => (skn_in_sign_msg n t1) 
| reveal t1 => (skn_in_sign_msg n t1) 
| sign t1 t2 => andb (match t1 with 
                                           | pi2 (k (N n')) => if  (beq_nat n' n) then true else true
                                                  | _ => true
                                                  end) (skn_in_sign_msg n t2) 
| i n' => true

| f  l => (@forallb message (skn_in_sign_msg n) l)

end.

(** [oursum]  *)

Definition  skn_in_sign_os (n : nat )(t:oursum) : bool :=
match t with
| msg t1 => (skn_in_sign_msg n t1)
| bol b => (skn_in_sign_bol n b)
end.

(** [mylist m] *)

Fixpoint  skn_in_sign_mylist (n : nat ){m}(t: mylist m) : bool :=
match t with
| []  => true
| h:: tl=> (andb (skn_in_sign_os n h)  (skn_in_sign_mylist  n tl)) 
end.
Eval compute in (sk 2).
Eval compute in skn_in_sign_msg 1 (sign (sk 2) O).

(** List of subterms of the form [sign ( sk(N n), t1),.....,sign ( sk(N n), tl)]. *)

Fixpoint list_skn_in_sign (n:nat) (l:list message) : list message :=
match l with 
| nil => nil
| cons h tl => (app (match h with 
            | sign (pi2 (k (N n'))) _ => if (beq_nat n' n) then (cons h nil) else nil
            | _ => nil
            end) 
             (list_skn_in_sign n tl))
end.
Eval compute in ( list_skn_in_sign 1 (subtrmls_msg (sign (ifm TRue (dec O (sk 1)) O) new))).

(** * Axioms *)

(** Correctness *)
Axiom correctness :  forall (n:nat) (t :message), (ver (pk n)  t (sign (sk n) t)) ## TRue.

(** Existential unforgeability under adaptively chosen message attacks (UF-CMA secure) *)

Fixpoint b  (j:nat) (k:nat) {n: nat} (ml: ilist message (n)) (t u :message) : Bool :=
 match j, ml with
   |  0 , _  => FAlse
   |  S _, []  => FAlse             
   | S j', h::tl => ifb  (eqm t h) (ver (pk k) h u) (b j' k tl t u)         
  end.    
 
Axiom UFCMA : forall (n l :nat)(ml: ilist message l) (t u: message), (clos_mylist [ msg t; msg u] = true) /\ (onlyin_pkrsk_mylist n [msg t; msg u] = true) /\ (skn_in_sign_mylist n [msg t; msg u] = true) /\ (l = length(list_skn_in_sign n (app ( subtrmls_msg t) ( subtrmls_msg u))))   ->  (ver (pk n) t u) ## (b l n ml t u).
 *)


Fixpoint insec_n_bol (n : nat )(t:Bool) : bool :=
  match t with 
    | eqb  b1 b2 =>  (orb (insec_n_bol n b1)  (insec_n_bol n b2))
    | eqm t1 t2 =>   orb (insec_n_msg n t1) ( insec_n_msg n t2)
    | ifb t1 t2 t3 =>  (orb (insec_n_bol n t1) (orb (insec_n_bol n t2) ( insec_n_bol n t3)))
    | EQL t1 t2 =>  (orb (insec_n_msg n t1) ( insec_n_msg n t2))
    | ver t1 t2 t3 => (orb (insec_n_msg n t1) (orb (insec_n_msg n t2) ( insec_n_msg n t3)))
    | _  => false
 end
with insec_n_msg (n : nat )(t:message) : bool :=
       match t with
         | N n' => (beq_nat n' n)
         | Mvar n' => false
         | ifm b t1 t2 => (orb (insec_n_bol n b) (orb (insec_n_msg n t1) ( insec_n_msg n t2)))
         | exp t1 t2 t3 =>  (orb (insec_n_msg n t1) (orb (insec_n_msg n t2) ( insec_n_msg n t3)))
         | pair t1 t2 =>  orb (insec_n_msg n t1) ( insec_n_msg n t2)
         | pi2 t1 => (message_beq (sk n) t)
         | pi1 t1 => match t1 with
                       | k (N _ ) => false
                       | _ => (insec_n_msg n t1)
                     end
                                        
         | ggen t1 =>  (insec_n_msg n t1)
         | act t1 =>  (insec_n_msg n t1)
         | rr t1 =>  (insec_n_msg n t1)
         | rs t1 =>  (insec_n_msg n t1)
         | L t1 =>  (insec_n_msg n t1)
         | m t1 =>  (insec_n_msg n t1)
         | enc t1 t2 t3 =>  (orb (insec_n_msg n t1) (orb (insec_n_msg n t2) ( insec_n_msg n t3)))
         | dec t1 t2 => orb (insec_n_msg n t1) ( insec_n_msg n t2)
         | k t1 =>  (insec_n_msg n t1) 
         | nc t1 => (insec_n_msg n t1) 
         | to t1 => (insec_n_msg n t1) 
         | reveal t1 => (insec_n_msg n t1) 
         | sign t1 t2 => match t1 with
                           | pi2 (k (N _)) => false
                           | _ => (orb (insec_n_msg n t1) (insec_n_msg n t2))
                         end
         | f  l => (@existsb message (insec_n_msg n) l)
         | _ => false
       end.

Eval compute in insec_n_msg 1   (pk 1). 
(** [oursum]  *)

Definition  insec_n_os (n : nat )(t:oursum) : bool :=
  match t with
    | msg t1 => (insec_n_msg n t1)
    | bol b => (insec_n_bol n b)
  end.

(** [mylist m] *)

Fixpoint  insec_n_mylis (n : nat ){m}(t: mylist m) : bool :=
  match t with
    | []  => false
    | h:: t => (orb (insec_n_os n h)  (insec_n_mylis  n t)) 
  end.
Eval compute in (sk 2).
Eval compute in insec_n_msg 1 (sign (sk 1) O).
(** remove duplicates in a list *)

  Fixpoint nodupmsg  (l : list message) : list message :=
    match l with
      | nil => nil
      | cons x xs => if checkmtlism x xs then nodupmsg xs else cons x (nodupmsg xs)
    end. 
 

(** List of subterms of the form [sign ( sk(N n), t1),.....,sign ( sk(N n), tl)]. *)

Fixpoint list_skn_in_sign (n:nat) (l:list message) : list message :=
  match l with 
    | nil => nil
    | cons h t => (app (match h with 
                          | sign (pi2 (k (N n'))) _ => if (beq_nat n' n) then (cons h nil) else nil
                          | _ => nil
                        end) 
                       (list_skn_in_sign n t))
  end. 
 
Definition distsigntrms n l := nodupmsg (list_skn_in_sign n l).    

Section ds_axioms.

(** * Digital Signatures*)
(** ** Assumptions *)



(** Correctness *)

  Axiom correctness :  forall (n:nat) (t :message), (ver (pk n)  t (sign (sk n) t)) ## TRue.

  
  
(** Existential unforgeability under adaptively chosen message attacks (UF-CMA secure) *)

  Fixpoint unforgb  (j:nat) (n:nat)  (ml: list message) (t u :message) : Bool :=
    match j, ml with
      |  0 , _ => FAlse
      |  S _, nil  => FAlse             
      | S j', cons h tl => match h with
                             | (sign ( pi2 (k (N n))) t1) =>   ifb  (eqm t t1) (ver (pk n) t1 u) (unforgb j' n tl t u)
                             | _ => FAlse
                           end
    end.    

  Axiom UFCMA : forall (n :nat)(t u: message), (clos_mylist [ msg t; msg u] = true) /\ (insec_n_mylis n [msg t; msg u] = false) ->
                                               let j := length(list_skn_in_sign n (app ( subtrmls_msg t) ( subtrmls_msg u))) in
                                               let ml := distsigntrms n (app ( subtrmls_msg t) ( subtrmls_msg u)) in
                                               (ver (pk n) t u) ## (unforgb j n ml t u).
 
End ds_axioms.