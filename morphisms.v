(************************************************************************)
(* Copyright (c) 2017, Ajay Kumar Eeralla <ae266@mail.missouri.edu>     *)
(*                   University of Missouri-Columbia.                   *)
(*                                                                      *)
(*                                                                      *)
(*                                                                      *)
(************************************************************************)

Load "definitions".

(** This library defines indistinguishability and all morphisms *)

(*Indistinguishability Relation ~*)
(*Definition Ind_Relation := forall n , mylist n -> mylist n -> Prop.*)

(** Indistinguishability relation [EQI]:
[[

forall n, relation (mylist n).
]]
 
 *)

Parameter EQI : forall {n }, relation (mylist n).

Notation "ml1 '~' ml2" := (EQI  ml1 ml2) (at level 0, right associativity).

Axiom EQI_equiv: forall n, equiv (mylist n) (@EQI n).

Instance EQI_Equiv :forall n, Equivalence  (@EQI n).
Proof.
split;
repeat apply EQI_equiv.
Qed. 

Theorem EQI_ref: forall {n:nat} (ml: mylist n), ml ~ ml.
Proof.
intros m.
apply EQI_equiv.
Qed.

Theorem EQI_sym: forall {n:nat} (ml1 ml2 : mylist n), ml1 ~ ml2 -> ml2 ~ ml1 .
Proof.
intros.
apply EQI_equiv.
assumption.
Qed.

Theorem EQI_trans : forall {n:nat} (ml1 ml2 ml3: mylist n), ml1 ~ ml2 -> ml2 ~ ml3 -> ml1 ~ ml3.
Proof.
  intros.  rewrite <- H in H0; auto.
Qed.

Add Parametric Relation n : (mylist n) (@EQI n)
reflexivity proved by (EQI_ref)
symmetry proved by (EQI_sym)
transitivity proved by (EQI_trans)
as EQI_rel.


(** Equivalence relation [EQm] defined on [message] type.  *)

Definition EQm : relation message := fun (m1:message)  (m2: message) =>  [bol (eqm m1 m2)] ~ [ bol TRue].

Notation "ml1 '#' ml2" := (EQm ml1 ml2) (at level 5).


Axiom EQm_equiv: equiv message EQm.

Instance EQm_Equiv : Equivalence  EQm.
Proof.
split;
repeat apply EQm_equiv.
Qed. 

Theorem EQm_ref: forall m:message, m # m.
Proof.
intros m.
apply EQm_equiv.
reflexivity.
Qed.

Theorem EQm_sym: forall m1 m2: message, m1 # m2 -> m2 # m1.
Proof.
intros.
rewrite H.
reflexivity.
Qed.


Theorem EQm_trans : forall m1 m2 m3 : message, m1 # m2 -> m2 # m3 -> m1 # m3.
Proof.
  intros.  rewrite <- H in H0; auto.
Qed.

(** Equivalence relation [EQb] defined on [Bool] type.  *)

Definition EQb : relation Bool := fun (b1:Bool)  (b2: Bool) =>  [bol (eqb b1 b2)] ~ [ bol TRue].
Notation "b1 '##' b2" := (EQb b1 b2) (at level 5).

Axiom BolEQ: equiv Bool EQb.

Instance Bol_Equ_Equiv : Equivalence  EQb.
Proof.
split;
repeat apply BolEQ.
Qed. 

Theorem EQb_sym: forall b1 b2:Bool, b1 ## b2 -> b2 ## b1.
Proof.
intros.
rewrite H.
reflexivity.
Qed.

Theorem EQb_ref: forall b:Bool, b ## b.
Proof.
intros.
reflexivity.
Qed.

Theorem EQb_trans : forall b1 b2 b3 : Bool, b1 ## b2 -> b2 ## b3 -> b1 ## b3.
Proof.
  intros.  rewrite <- H in H0; auto.
Qed.



(** Equivalence relation [EQos] on [oursum] type. *)

Inductive EQos :  relation oursum := 
|  eqm1: forall (m1 m2: message), m1 # m2 ->  EQos (msg m1) (msg m2)
|  eqb1: forall (b1 b2: Bool), b1 ## b2 ->  EQos (bol b1) (bol b2).

Notation "ml1 '###' ml2" := (EQos ml1 ml2) (at level 5).

Instance os_Equ_Equiv : Equivalence  EQos.
Proof.
split.
unfold Reflexive;
intros;
destruct x;
try apply eqm1; try apply eqb1;
reflexivity.
unfold Symmetric; intros; destruct H;  
    try apply eqm1; try apply eqb1; symmetry; assumption.
unfold Transitive; intros.
  inversion H; subst;
  inversion H0; subst;
  try apply  eqm1; try apply eqb1;   
  rewrite H1;
  apply H3.   

Qed.  
 
Theorem EQos_sym: forall b1 b2: oursum, b1 ### b2 -> b2 ### b1.
Proof.
intros.
rewrite H.
reflexivity.
Qed.

Theorem EQos_ref: forall b:oursum, b ### b.
Proof.
intros.
reflexivity.
Qed.

Theorem EQos_trans : forall b1 b2 b3 : oursum, b1 ### b2 -> b2 ### b3 -> b1 ### b3.
Proof.
  intros.  rewrite <- H in H0; auto.
Qed.

(** Equivalence relation [EQosl] is defined on [mylist n] for a natural number [n]. *)

Inductive EQosl: forall {n:nat}, relation (mylist n) :=
| eqnos :  EQosl  (Nil _) (Nil _)
| eqconos: forall (m:nat)(os1 os2:oursum)(l1 l2: mylist m), os1 ### os2 -> (EQosl  l1  l2) -> EQosl (os1 :: l1) (os2::l2).

Notation "ml1 '####' ml2" := (EQosl ml1 ml2) (at level 0).

Axiom eqlistos_ind: forall (n:nat) (l1 l2: mylist n), l1 #### l2 ->  l1 ~ l2.

Instance osl_Equ_Equiv {n}: Equivalence  (@EQosl n).
Proof.
split.
  unfold Reflexive.
  induction x.
   apply eqnos.
   apply eqconos. reflexivity. apply IHx.
 unfold Symmetric.
intros  x y H.
induction H.
apply eqnos.
apply eqconos.
rewrite H. reflexivity. apply IHEQosl.
unfold Transitive.
 intros x y z H1 H2. 
 induction H1. assumption. 
  + dependent destruction z.
     - apply eqconos;    inversion H2; subst. rewrite H. apply H6.
        dependent destruction H2. apply   IHEQosl . assumption.
Qed.

(** Equivalence relation [EQlm] defined on [list message] type. *)

Inductive EQlm:  relation (list message) :=
| eqnm :  EQlm nil nil
| eqconm: forall (m1 m2 : message)(l1 l2: list message),  m1 # m2 -> (EQlm  l1  l2) -> EQlm (cons m1 l1) (cons m2 l2).
Notation "ml1 '#@' ml2" := (EQlm ml1 ml2) (at level 0).
Axiom eqlistm_ind: forall  (l1 l2:  list message ), l1 #@ l2 ->  (f l1) # (f l2).
Instance EQlm_Equ_Equiv : Equivalence  (EQlm).
Proof.
split.
  unfold Reflexive.
  induction x.
   apply eqnm.
   apply eqconm. reflexivity. apply IHx.
 unfold Symmetric.
intros  x y H.
induction H.
apply eqnm.
apply eqconm.
rewrite H. reflexivity. apply IHEQlm.
unfold Transitive.
 intros x y z H1 H2. 
 induction H1. assumption. 
  Admitted.
  
Axiom EQlm_equiv:  equiv (list message) (EQlm).

Instance lm_Eqlm_Equiv : Equivalence  (EQlm ).
Proof.
split;
repeat apply EQlm_equiv.
Qed. 

(** * Morhphisms *)

Axiom eq_msg_mylist_Cong :  forall  (n n1 :nat) (m1 m2: message) (l1 l2: mylist n), m1 # m2 -> l1 #### l2 ->  (submsg_mylist n1 m1 l1) ~ (submsg_mylist n1 m2 l2).

Add Parametric Morphism{n}: (@ submsg_mylist n ) with
  signature eq ==> EQm ==> EQosl ==> EQI as submsg_mor.
 Proof.   intros. apply eq_msg_mylist_Cong; assumption. Qed.

Axiom f_Cong_l : forall (l1 l2: list message) (m1 m2:message), m1 # m2 -> l1 #@ l2   -> (cons m1 l1 ) #@ (cons m2 l2). 
Add Parametric Morphism : cons  with
  signature EQm ==> EQlm ==> EQlm as cons_m.
 Proof.    intros. apply f_Cong_l. assumption.  assumption. Qed.

Add Parametric Morphism : f  with
  signature EQlm ==> EQm as f_m.
 Proof.    intros. apply eqlistm_ind. assumption.   Qed.

(**split.
  unfold Reflexive.
  induction x.
   apply EQNm.

   apply EQCONSm. reflexivity. apply IHx.

 unfold Symmetric.

intros  x y H.

induction H.
apply EQNm.
apply EQCONSm.
rewrite H. reflexivity. apply IHEQlm.

unfold Transitive.
 intros x y z H1 H2. 
 induction H1.
   +  apply H2.
  + dependent destruction z.
     - rewrite <- H2. apply EQCONSm;    inversion H2; subst. rewrite H. apply H6.
        dependent destruction H2. apply   IHEQosl . assumption.
Qed.

Qed.*)

(** * [message] *)

(** [exp_mor] *)
Axiom exp_Cong: forall (m1 m2 m3 m1' m2' m3' : message), m1 # m1' -> m2 # m2' -> m3 # m3' -> (exp m1 m2 m3) # (exp m1' m2' m3').
Add Parametric Morphism: (@ exp) with
  signature EQm ==> EQm ==> EQm ==> EQm as exp_mor.
 Proof.   intros. apply exp_Cong; assumption. Qed.

(** [pair_mor] *)

Axiom pair_Cong: forall (m1 m2  m1' m2'  : message), m1 # m1' -> m2 # m2'  -> (pair m1 m2) # (pair m1' m2').
Add Parametric Morphism: (@ pair) with
  signature EQm ==> EQm ==> EQm as pair_mor.
 Proof.   intros. apply pair_Cong; assumption. Qed.

(** [pi1_mor] *)

Axiom pi1_Cong: forall (m1 m1' : message), m1 # m1' -> (pi1 m1) # (pi1 m1' ).
Add Parametric Morphism: (@ pi1) with
  signature EQm ==> EQm as pi1_mor.
 Proof.   intros. apply pi1_Cong; assumption. Qed.

(** [pi2_mor] *)

Axiom pi2_Cong: forall (m1 m1' : message), m1 # m1' -> (pi2 m1) # (pi2 m1' ).
Add Parametric Morphism: (@ pi2) with
  signature EQm ==> EQm as pi2_mor.
 Proof.   intros. apply pi2_Cong; assumption. Qed.

(** [ggen_mor] *)

Axiom ggen_Cong: forall (m1 m1' : message), m1 # m1' -> (ggen m1) # (ggen m1' ).
Add Parametric Morphism: (@ ggen) with
  signature EQm ==> EQm as ggen_mor.
 Proof.   intros. apply ggen_Cong; assumption. Qed.

(** [r_mor] *)

Axiom r_Cong: forall (m1 m1' : nat), m1 = m1' -> (r m1) # (r m1' ).
Add Parametric Morphism: (@ r) with
  signature eq ==> EQm as r_mor.
Proof. intros. apply r_Cong. reflexivity. Qed.

(** [rs_mor] *)

Axiom rs_Cong: forall (m1 m1' : message), m1 # m1' -> (rs m1) # (rs m1' ).
Add Parametric Morphism: (@ rs) with
  signature EQm ==> EQm as rs_mor.
 Proof.   intros. apply rs_Cong; assumption. Qed.

(** [act_mor] *)

Axiom act_Cong: forall (m1 m1' : message), m1 # m1' -> (act m1) # (act m1' ).
Add Parametric Morphism: (@ act) with
  signature EQm ==> EQm as act_mor.
 Proof.   intros. apply act_Cong; assumption. Qed.

(** [m_mor] *)

Axiom m_Cong: forall (m1 m1' : message), m1 # m1' -> (m m1) # (m m1' ).
Add Parametric Morphism: (@ m) with
  signature EQm ==> EQm as m_mor.
 Proof.   intros. apply m_Cong; assumption. Qed.

(** [nonce_mor] *)

Axiom nonce_Cong: forall (m1 m1' : message), m1 # m1' -> (nc m1) # (nc m1' ).
Add Parametric Morphism: (@ nc) with
  signature EQm ==> EQm as nonce_mor.
Proof. intros. apply nonce_Cong. assumption.  Qed.

(** [to_mor] *)

Axiom to_Cong: forall (m1 m1' : message), m1 # m1' -> (to m1) # (to m1' ).
Add Parametric Morphism: (@ to) with
  signature EQm ==> EQm as to_mor.
 Proof.   intros. apply to_Cong; assumption. Qed.

 (** [reveal_mor] *)
 
Axiom reveal_Cong: forall (m1 m1' : message), m1 # m1' -> (reveal m1) # (reveal m1' ).
Add Parametric Morphism: (@ reveal) with
  signature EQm ==> EQm as reveal_mor.
 Proof.   intros. apply reveal_Cong; assumption. Qed.
(*
(******************reveal signature**********************)
Axiom revsign_Cong: forall (m1 m1' : nat), m1 = m1' -> (revsign m1) ## (revsign m1' ).
Add Parametric Morphism: (@ revsign) with
  signature eq ==> EQb as revsign_mor.
 Proof.   intros. apply revsign_Cong. reflexivity. Qed.
*)
 (** [sign_mor] *)
 
Axiom sign_Cong: forall (m1 m1' m2 m2' : message), m1 # m1' -> m2 # m2' -> (sign m1 m2) # (sign m1' m2' ).
Add Parametric Morphism: (@sign) with
  signature EQm ==> EQm ==> EQm as sign_mor.
 Proof.   intros. apply sign_Cong; assumption. Qed.

 (** [enc_mor] *)
 
Axiom enc_Cong: forall (m1 m2 m3 m1' m2' m3' : message), m1 # m1' -> m2 # m2' -> m3 # m3'  -> (enc m1 m2 m3) # (enc m1' m2' m3').
Add Parametric Morphism: (@ enc) with
  signature EQm ==> EQm ==> EQm ==> EQm as enc_mor.
Proof.   intros. apply enc_Cong; assumption. Qed.

(** [L_mor] *)

Axiom L_Cong: forall (m1  m1'  : message), m1 # m1'  -> (L m1) # (L m1').
Add Parametric Morphism: (@ L) with
  signature EQm ==> EQm as L_mor.
 Proof.   intros. apply L_Cong; assumption. Qed.

 (** [dec_mor] *)
 
Axiom dec_Cong: forall (m1 m2  m1' m2'  : message), m1 # m1' -> m2 # m2'  -> (dec m1 m2) # (dec m1' m2').
Add Parametric Morphism: (@ dec) with
  signature EQm ==> EQm ==> EQm as dec_mor.
 Proof.   intros. apply dec_Cong; assumption. Qed.

(** [k_mor] *)

Axiom k_Cong: forall (m1 m1' : message), m1 # m1' -> (k m1) # (k m1' ).
Add Parametric Morphism: (@ k) with
  signature EQm ==> EQm as k_mor.
 Proof.   intros. apply k_Cong; assumption. Qed.

(** [pk_mor] *) 

Axiom pk_Cong: forall (m1 m1' : nat), m1 = m1' -> (pk m1) # (pk m1' ).
Add Parametric Morphism: (@ pk) with
  signature eq ==> EQm as pk_mor.
 Proof.   intros. apply pk_Cong. reflexivity. Qed.

(** [sk_mor] *)

Axiom sk_Cong: forall (m1 m1' : nat), m1 = m1' -> (sk m1) # (sk m1' ).
Add Parametric Morphism: (@ sk) with
  signature eq ==> EQm as sk_mor.
 Proof.   intros. apply sk_Cong. reflexivity. Qed.

 (** [f_mor] *)
 
Axiom f_Cong: forall (l1 l1' : list message), ( l1) #@ ( l1') -> (f  l1) # (f  l1' ).
Add Parametric Morphism : ( f ) with
  signature EQlm ==> EQm as f_mor.
Proof.   intros. apply f_Cong. assumption. Qed.

(** * [Bool] *)

(** [ifb_mor] *)

Axiom IFB_Cong: forall (b1 b2 b3 b1' b2' b3': Bool), b1 ## b1' -> b2 ## b2' -> b3 ## b3' -> (ifb b1 b2 b3) ## (ifb b1' b2' b3').
Add Parametric Morphism: (@ifb) with
  signature EQb ==> EQb ==> EQb ==> EQb as ifb_mor.
 Proof.   intros. apply IFB_Cong; assumption. Qed.

(** [ifm_mor] *)

 Axiom IFM_Cong: forall (b b' : Bool) ( m1 m2 m1' m2': message), (b ## b') -> m1 # m1' -> m2 # m2' -> (ifm b m1 m2) # (ifm b' m1' m2').
Add Parametric Morphism: (@ifm) with
  signature EQb ==> EQm ==> EQm ==> EQm as ifm_mor.
 Proof.   intros. apply IFM_Cong; assumption. Qed.

 (** [eqb_mor] *)
 
Axiom eqb_Cong: forall (b1 b2 b1' b2': Bool),  b1 ## b1' -> b2 ## b2' ->  (eqb b1 b2) ## (eqb b1' b2').
Add Parametric Morphism: (@eqb) with
signature EQb ==> EQb ==> EQb as eqb_mor.
Proof.   intros. apply eqb_Cong; assumption. Qed.

(** [eqm_mor] *)

Axiom eqm_Cong: forall (m1 m2 m1' m2' : message), m1 # m1' -> m2 # m2' -> (eqm m1 m2) ## (eqm m1' m2').

Add Parametric Morphism: (@eqm) with
  signature EQm ==> EQm ==> EQb as eqm_mor.
 Proof.   intros. apply eqm_Cong; assumption. Qed.

(** [EQ_L_mor] *)
Axiom EQL_Cong : forall (m1 m2 m1' m2' : message), m1 # m1' -> m2 # m2' -> (EQL m1 m2 ) ## (EQL m1' m2').
Add Parametric Morphism: (@EQL) with
  signature EQm ==> EQm ==> EQb as EQL_mor.
Proof.   intros. apply EQL_Cong; assumption. Qed.

(** [ver_mor] *)

Axiom ver_Cong : forall (m1 m2  m3 m1' m2' m3' : message), m1 # m1' -> m2 # m2' -> m3 # m3' -> (ver m1 m2 m3 ) ## (ver m1' m2' m3').
Add Parametric Morphism: (@ver) with
  signature EQm ==> EQm ==> EQm ==> EQb as ver_mor.
Proof.   intros. apply ver_Cong; assumption. Qed.


(** * Morphisms on substitution functions *)

(** [substbl_bl_mor] *)

Axiom substbl_bl_Cong : forall (b1 b2 b1' b2' : Bool) (n: nat), b1 ## b1' -> b2 ## b2' -> (subbol_bol n b1 b2) ## (subbol_bol n b1' b2').

Add Parametric Morphism : (@subbol_bol) with
signature eq ==> EQb ==> EQb ==> EQb as substbl_bl_mor.
Proof. intros.  apply substbl_bl_Cong. apply H. apply H0.
Qed.

(** [substbl_msg_mor] *)

Axiom substbl_msg_Cong : forall (b1 b1' : Bool)(m2 m2' : message) (n: nat), b1 ## b1' -> m2 # m2' -> (subbol_msg n b1 m2) # (subbol_msg n b1' m2').

Add Parametric Morphism : (@subbol_msg) with
signature eq ==> EQb ==> EQm ==> EQm as substbl_msg_mor.
Proof. intros.  apply substbl_msg_Cong. apply H. apply H0.
Qed.

(** [substmsg_Bool_mor] *)

Axiom substmsg_Bool_Cong : forall (m1 m1' : message) (b1 b1' : Bool) (n: nat), m1 # m1' -> b1 ## b1' -> (submsg_bol n m1 b1) ## (submsg_bol n m1' b1').

Add Parametric Morphism : (@submsg_bol) with
signature eq ==> EQm ==> EQb ==> EQb as substmsg_Bool_mor.
Proof. intros.  apply substmsg_Bool_Cong. apply H. apply H0.
Qed.

(** [substmsg_msg_mor] *)

Axiom substmsg_msg_Cong : forall (m1 m2 m1' m2' : message) (n: nat), m1 # m1' -> m2 # m2' -> (submsg_msg n m1 m2) # (submsg_msg n m1' m2').

Add Parametric Morphism : (@submsg_msg) with
signature eq ==> EQm ==> EQm ==> EQm as substmsg_msg_mor.
Proof. intros.  apply substmsg_msg_Cong. apply H. apply H0.
Qed.

(** [subbol_msg'_mor] *)

Axiom clos_subbol_cong : forall ( b1 b2 b3 b4: Bool) (t1 t2:message), b1 ## b2 -> b3 ## b4 -> t1 # t2 -> (subbol_msg' b1 b3 t1) # (subbol_msg' b2 b4 t2).

Add Parametric Morphism : subbol_msg'  with
  signature EQb ==> EQb ==> EQm ==> EQm as subbol_msg'_mor.
 Proof.   intros. apply clos_subbol_cong; try assumption. Qed.

(** * [oursum] *)
(** [msg_mor] *)

Axiom msg_Cong: forall (m1 m1'  : message), m1 # m1'  -> (msg m1 ) ### (msg m1').

Add Parametric Morphism : (@msg ) with
signature EQm ==> EQos as msg_mor.
Proof. intros. apply eqm1. apply H. Qed.

(** [bol_mor] *)

Axiom bol_Cong: forall (b1 b1'  : Bool), b1 ## b1'  -> (bol b1 ) ### (bol b1').

Add Parametric Morphism : (@bol ) with
signature EQb ==> EQos as bol_mor.
Proof.  intros. apply eqb1. apply H. Qed. 

(** [Cons_mor] *)

Add Parametric Morphism {n}: (Cons oursum n) with
signature EQos ==> EQosl ==> EQosl  as Cons_mor.
Proof. intros. apply eqconos. apply H. apply H0. Qed. 

(** [app_EQml_mor] *)

Axiom app_EQml_Cong : forall (n1 n2:nat)(l1 l1'  : mylist n1) (l2 l2': mylist n2), l1 #### l1' -> l2 ####l2' -> (l1 ++ l2) #### (l1' ++ l2').

Add Parametric Morphism {n1} {n2}: (@app_mylist n1 n2 ) with
signature  EQosl ==> EQosl ==> EQosl  as app_EQml_mor.
Proof. intros. apply app_EQml_Cong. apply H. apply H0. Qed. 

(** [ml_EQI_mor] *)

Axiom ml_EQI_Cong: forall (n : nat) (l1 l2 : mylist n) (os1 os2 : oursum), os1 ### os2 -> l1 ####l2 -> (Cons oursum n os1 l1 ) ~ (Cons  oursum n os2 l2) .

Add Parametric Morphism {n}: (Cons oursum n) with
signature EQos ==> EQosl ==> EQI  as ml_EQI_mor.

Proof. intros. apply ml_EQI_Cong with (os1:=x) (os2:=y) (l1:= x0) (l2:= y0). apply H. apply H0. Qed.

(** [app_EQI_mor] *)

Axiom app_EQI_Cong : forall (n1 n2:nat)(l1 l1'  : mylist n1) (l2 l2': mylist n2), l1 #### l1' -> l2 ####l2' -> (l1 ++ l2) ~ (l1' ++ l2').

Add Parametric Morphism {n1} {n2}: (@app_mylist n1 n2 ) with
signature  EQosl ==> EQosl ==> EQI  as app_EQI_mor.
Proof. intros. apply app_EQI_Cong. apply H. apply H0. Qed.


(** Equivalence relation [EQml] on [ilist message n] for given [n]. *)

Definition EQml {n:nat} (l1 l1': ilist message n) :=  (EQosl (conv_mlist_mylist l1) (conv_mlist_mylist l1')).

Notation "ml1 '==' ml2" := (EQml ml1 ml2) (at level 0).

Theorem eqlistm_ind': forall (n:nat) (l1 l2: ilist message n), (l1 == l2) ->  (conv_mlist_mylist l1) ~ (conv_mlist_mylist l2).
Proof. intros. apply eqlistos_ind. apply H. Qed.

Instance ml_Equ_Equiv {n}: Equivalence  (@EQml n).
Proof. 
split.
unfold EQml.
unfold Reflexive. reflexivity.
unfold EQml. unfold Symmetric. intros. rewrite H. reflexivity. 
unfold EQml. unfold Transitive. intros. rewrite H, H0. reflexivity.
Qed.

(** andB_mor *)

Axiom andB_Cong: forall (b1 b2 b1' b2' : Bool), b1 ## b1' -> b2 ## b2' -> (b1 & b2) ## (b1' & b2').

Add Parametric Morphism:(@ andB) with 
signature EQb ==> EQb ==> EQb as andB_mor.
Proof. intros. apply andB_Cong;assumption. Qed.

(** notb_mor *)

Axiom notb_Cong : forall (b1 b1' : Bool), b1 ## b1' -> (notb b1) ## (notb b1').

Add Parametric Morphism: (@ notb) with
signature EQb ==> EQb as notb_mor.
Proof. 
intros.
apply notb_Cong.
assumption. Qed.

(** Equality of [Bool] terms using indistinguishability. *)

Definition EQI_bol (b1 b2: Bool) := [ bol (eqb b1 b2)] ~ [bol TRue].

Notation "b1 ## b2" := (EQI_bol b1 b2)(at level 5). 

(** Equality of [message] terms using indistinguishability. *)

Definition EQI_msg (x y : message) :=  [ bol (eqm x y)] ~ [ bol TRue] .

Notation "m1 # m2" := (EQI_msg m1 m2)(at level 5).

(** Attacker starts new session. *)

Definition Att_new_session:= forall x:message,  (eqm (act x) new)  ## TRue .

