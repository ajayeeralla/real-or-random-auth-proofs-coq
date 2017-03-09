Load "tactics1".

(*************IFTF******************************************)
(******if b then true else false = b***********************)


Theorem IFTF:  forall (n:nat),  (if_then_else_B (Bvar n) TRue FAlse) ## (Bvar n).
Proof.
intros.

rewrite <- (IFSAME_B (Bvar n) (Bvar n)) at 2.
rewrite -> IFEVAL_B with (b1 := (Bvar n)).
simpl.
rewrite <- beq_nat_refl.
reflexivity.
Qed.


Theorem IFTFb : forall (b:Bool),  (if_then_else_B b TRue FAlse) ## b.
  Proof. intros;pose proof(IFTF 0); apply Forall_ELM_EVAL_B with (n:=0) (b:=b) in H; simpl in H; auto. Qed.