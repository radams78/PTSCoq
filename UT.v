Require Export PTS.
Require Import CR.
Require Import Meta.

Axiom func_ax : forall (s t t' : sort), axiom s t -> axiom s t' -> t = t'.
Axiom func_rule : forall (s1 s2 s3 s3' : sort), rule s1 s2 s3 -> rule s1 s2 s3' -> s3 = s3'.

Theorem Unique_Types :
  forall n (M : term n) Gamma A B, Gamma |- M ; A -> Gamma |- M ; B -> A ~= B.
Proof.
  induction M; intros.
(* Variable f *)
  apply conv_trans with (typeof f Gamma).
   apply conv_sym.
     apply Gen_var.
     assumption.
   apply Gen_var.
     assumption.
(* Sort s *)
  elim Gen_srt with n Gamma s A.
   intro t.
     destruct 1.
     elim Gen_srt with n Gamma s B.
      intro t'.
        destruct 1.
	apply conv_trans with (srt (n:=n) t).
	 apply conv_red.
	   assumption.
	 rewrite func_ax with s t t'; auto.
	   apply conv_sym.
	   apply conv_red.
	   assumption.
      assumption.
   assumption.
(* Application *)
   elim Gen_app with n Gamma M1 M2 A.
    intro C.
      destruct 1.
      rename x into D.
      destruct H1.
      destruct H2.
      elim Gen_app with n Gamma M1 M2 B.
       intro C'.
         destruct 1.
	 rename x into D'.
	 destruct H4.
	 destruct H5.
	 apply conv_trans with (subbot D M2).
	  assumption.
	  apply conv_trans with (subbot D' M2).
	   apply conv_subbot.
	    apply conv_pi_injr with C C'.
	      apply IHM1 with Gamma; assumption.
	    apply conv_ref.
           apply conv_sym.
	     assumption.
       assumption.
    assumption.
(* Product *)
   elim Gen_pi with n Gamma M1 M2 A.
    intro s1.
      destruct 1.
      rename x into s2.
      destruct H1.
      rename x into s3.
      destruct H1.
      destruct H2.
      destruct H3.
      elim Gen_pi with n Gamma M1 M2 B.
       intro t1.
         destruct 1.
	 rename x into t2.
	 destruct H5.
	 rename x into t3.
	 destruct H5.
	 destruct H6.
	 destruct H7.
	 apply conv_trans with (srt (n:=n) s3).
	  apply conv_red.
	    assumption.
	  rewrite func_rule with s1 s2 s3 t3.
	   apply conv_sym.
	     apply conv_red.
	     assumption.
	   assumption.
	   rewrite conv_srt_inj with n s1 t1.
	    rewrite conv_srt_inj with (S n) s2 t2.
	     assumption.
	     apply IHM2 with (Gamma, M1); assumption.
	     apply IHM1 with Gamma; assumption.
       assumption.
    assumption.
(* Abstraction *)
   elim Gen_lda with n Gamma M1 M2 A.
    intro C.
      destruct 1.
      rename x into s3.
      destruct H1.
      destruct H2.
      elim Gen_lda with n Gamma M1 M2 B.
       intro C'.
         destruct 1.
	 rename x into t3.
	 destruct H4.
	 destruct H5.
	 apply conv_trans with (pi M1 C).
	  assumption.
	  apply conv_trans with (pi M1 C').
	   apply conv_pi.
	    apply conv_ref.
	    apply IHM2 with (Gamma, M1); assumption.
	   apply conv_sym.
	     assumption.
       assumption.
    assumption.
Qed.
