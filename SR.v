Require Export PTS.
Require Import CR.
Require Import Meta.

Lemma Subject_par_Reduction : forall n (Gamma : context n) M A,
  Gamma |- M ; A ->
  forall Gamma' M',
  Gamma |c> Gamma' -> M |> M' -> Gamma' |- M' ; A.
Proof.
  induction 1.
(* axioms *)
   destruct Gamma'.
     intros.
     rewrite Gen_par_red1_srt with O s M'.
      apply axioms.
        assumption.
      assumption.
(* start *)
   destruct Gamma'.
     fold context in c.
     rename c into Delta.
     rename t into B.
     intros.
     assert (Gamma |c> Delta).
       apply par_red1_ctxt_injl with A B.
       assumption.
     assert (Delta |- B ; srt s).
       apply IHPTS.
        assumption.
	apply par_red1_ctxt_injr with Gamma Delta.
	  assumption.
     rewrite Gen_par_red1_var with (S n) (bot (n:=n)) M'.
      apply conversion with (liftterm B) s.
       apply conv_sym.
         apply conv_par_red1.
	 exact (H0 bot).
       apply start with s.
         assumption.
       apply weakening with (B := srt (n:=n) s) (s := s); auto.
      assumption.
(* weakening *)
   destruct Gamma'.
     fold context in c.
     rename c into Delta.
     rename t into D.
     intros.
     assert (Gamma |c> Delta).
       apply par_red1_ctxt_injl with C D.
       assumption.
     elim par_red1_liftterm_inv with n A M'.
      intro A'.
        destruct 1.
	rewrite H4.
	apply weakening with s; auto.
	apply IHPTS2.
	 assumption.
	 apply par_red1_ctxt_injr with Gamma Delta.
           assumption.
      assumption.
(* product *)
   intros.
     elim Gen_par_red1_pi with n A M' B.
      intro A'.
        destruct 1.
	rename x into B'.
	destruct H4.
	destruct H5.
	rewrite H6.
	apply product with s1 s2.
	 assumption.
	 apply IHPTS1; assumption.
	 apply IHPTS2.
	  apply par_red1_ctxt_build; assumption.
	  assumption.
      assumption.
(* application *)
   intros.
     elim Gen_par_red1_app with n F a M'.
      (* Case M' = F' a', where F |> F' and a |> a' *)
      destruct 1.
        rename x into F'.
	destruct H3.
	rename x into a'.
	destruct H3.
	destruct H4.
	rewrite H5.
	assert (Gamma' |- F' ; pi A B).
	  apply IHPTS1; assumption.
	elim Type_Validity with n Gamma' F' (pi A B).
	 destruct 1.
	   discriminate H7.
	 destruct 1.
	   rename x into s3.
	   elim Gen_pi' with n Gamma' A B s3.
	    intro s1.
	      destruct 1.
	      rename x into s2.
	      destruct H8.
	      destruct H9.
	      apply conversion with (subbot B a') s2.
	       apply conv_subbot.
	        apply conv_ref.
		apply conv_sym.
		  apply conv_par_red1.
		  assumption.
	       apply application with A; auto.
	       apply Substitution_bot with (B := srt (n:=S n) s2) (N := a) (A := A); auto.
	    assumption.
	 assumption.
      (* Case F = lda A' R, a |> a', R |> R', M' = subbot R' Q' *)
      destruct 1.
        rename x into A'.
	destruct H3.
	rename x into a'.
	destruct H3.
	rename x into R.
	destruct H3.
	rename x into R'.
	destruct H3.
	destruct H4.
	destruct H5.
	rewrite H6.
	elim Gen_lda' with n Gamma' A' R' (pi A B).
	 intro B'.
	   destruct 1.
	   rename x into s1.
	   destruct H7.
	   rename x into s2.
	   destruct H7.
	   rename x into s3.
	   destruct H7.
	   destruct H8.
	   destruct H9.
	   destruct H10.
	   assert (Gamma' |- F ; pi A B).
	     auto.
	   elim Type_Validity with n Gamma' F (pi A B).
	    destruct 1.
	      discriminate H13.
	    destruct 1.
	      rename x into t3.
	      elim Gen_pi' with n Gamma' A B t3.
	       intro t1.
	         destruct 1.
		 rename x into t2.
		 destruct H14.
		 destruct H15.
		 apply conversion with (subbot B' a') t2.
		  apply conv_sym.
		    apply conv_subbot. 
	             apply conv_pi_injr with A A'.
	               assumption.
		     apply conv_par_red1.
	               assumption.
	          apply Substitution_bot with A'.
		   apply conversion with A s1; auto.
 	             apply conv_pi_injl with B B'.
		     assumption.
		   assumption.
		  apply Substitution_bot with (B := srt (n:=S n) t2) (N := a) (A := A); auto.
		assumption.
	    assumption.
	 apply IHPTS1.  
	  assumption.
	  rewrite H3.
	    apply par_red1_lda.
	     apply par_red1_ref.
	     assumption.
      assumption.
(* abstraction *)
   intros.
     elim Gen_par_red1_lda with n A M' b.
      intro A'.
        destruct 1.
	rename x into b'.
	destruct H5.
	destruct H6.
	rewrite H7.
	apply conversion with (pi A' B) s3.
	 apply conv_pi.
	  apply conv_sym.
	    apply conv_par_red1.
	    assumption.
	  apply conv_ref.
	 apply abstraction with s1 s2 s3.
	  assumption.
	  apply IHPTS1.
	   apply par_red1_ctxt_build; assumption.
	   assumption.
	  apply IHPTS2; assumption.
	  apply IHPTS3.
	   apply par_red1_ctxt_build; assumption.
	   apply par_red1_ref.
	 apply product with s1 s2.
	  assumption.
	  auto.
	  apply IHPTS3.
	   apply par_red1_ctxt_build; auto.
	   apply par_red1_ref.
	assumption.
(* conversion *)
   intros.
     apply conversion with B s; auto.
Qed.

Theorem Subject_Reduction : forall n (Gamma : context n) M M' A,
  Gamma |- M ; A -> M ->> M' -> Gamma |- M' ; A.
Proof.
  induction 2.
  apply Subject_par_Reduction with Gamma M; auto.
  apply IHred2.
  apply IHred1.
  assumption.
Qed.

Theorem Predicate_Reduction : forall n (Gamma : context n) M A B,
  Gamma |- M ; A -> A ->> B -> Gamma |- M ; B.
Proof.
  intros.
  elim Type_Validity with n Gamma M A.
   destruct 1.
     rename x into s.
     rewrite Gen_red_srt with n s B; rewrite <- H1; assumption.
   destruct 1.
     rename x into s.
     apply conversion with A s.
      apply conv_red.
        assumption.
      assumption.
      apply Subject_Reduction with A; assumption.
   assumption.
Qed.

Theorem conversion' : forall n (Gamma : context n) M N A B, Gamma |- M ; A -> A ~= B -> Gamma |- N ; B -> Gamma |- M ; B.
Proof.
intros.
elim Type_Validity with n Gamma N B.
 destruct 1.
   rewrite H2.
   apply Predicate_Reduction with A.
    assumption.
      apply Gen_conv_srt.
      rewrite <- H2.
      assumption.
    destruct 1.
      rename x into s.
      apply conversion with A s; assumption.
 assumption.
Qed.