Require Import Bool.
Require Import Arith.
Require Export String.
Require Import CR.
Require Import Meta.
Require Import SR.

Coercion Is_true : bool >-> Sortclass.

Fixpoint varlike (n : nat) (M : term n) {struct M} : bool :=
match M with
  var n x => true |
  srt n s => false |
  app n M N => varlike n M |
  pi n A B => false |
  lda n A M => varlike (S n) M
end.

Implicit Arguments varlike [n].

Lemma varlike_subvar : forall m M n (rho : fin m -> fin n),
  varlike M -> varlike (subvar M rho).
Proof.
 induction M; simpl; auto.
Qed.

Lemma varlike_subvar' : forall m M n (rho : fin m -> fin n),
  varlike (subvar M rho) -> varlike M.
Proof.
 induction M; simpl; auto.
 intros n0 rho.
 apply IHM2.
Qed.

Fixpoint sortlike (n : nat) (M : term n) {struct M} : bool :=
match M with
  var n x => false |
  srt n s => true |
  app n M N => sortlike n M |
  pi n A B => true |
  lda n A M => sortlike (S n) M
end.

Implicit Arguments sortlike [n].

Lemma sortlike_subvar : forall m M n (rho : fin m -> fin n),
  sortlike M -> sortlike (subvar M rho).
Proof.
 induction M; simpl; auto.
Qed.

Lemma sortlike_subvar' : forall m M n (rho : fin m -> fin n),
  sortlike (subvar M rho) -> sortlike M.
Proof.
 induction M; simpl; auto.
 intros n0 rho.
 apply IHM2.
Qed.

Lemma sortlike_liftterm : forall n (M : term n), sortlike M -> sortlike (liftterm M).
Proof.
intros.
unfold liftterm.
apply sortlike_subvar.
assumption.
Qed.

Lemma sortlike_liftterm' : forall n (M : term n), sortlike (liftterm M) -> sortlike M.
Proof.
unfold liftterm.
intros n M.
apply sortlike_subvar'.
Qed.

Lemma var_or_sort : forall n (M : term n), varlike M \/ sortlike M.
Proof.
 induction M; simpl; auto.
Qed.

Lemma var_not_sort : forall n (M : term n), varlike M -> sortlike M -> False.
Proof.
 induction M; simpl; auto.
Qed.

Lemma Unique_Type_varlike : forall n (M : term n), varlike M -> 
  forall Gamma A B, Gamma |- M ; A -> Gamma |- M ; B -> A ~= B.
Proof.
 induction M; simpl.
  intros _ Gamma A B H H1.
    apply conv_trans with (typeof f Gamma).
     apply conv_sym.
       apply Gen_var.
       assumption.
     apply Gen_var.
       assumption.
  destruct 1.
  intros.
    elim Gen_app with n Gamma M1 M2 A.
     intro C.
       destruct 1.
       rename x into D.
       destruct H2.
       destruct H3.
       elim Gen_app with n Gamma M1 M2 B.
        intro C'.
	  destruct 1.
	  rename x into D'.
	  destruct H5.
	  destruct H6.
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
  destruct 1.
  intros.
    elim Gen_lda with n Gamma M1 M2 A.
     intro C.
       destruct 1.
       rename x into s.
       destruct H2.
       destruct H3.
       elim Gen_lda with n Gamma M1 M2 B.
        intro C'.
	  destruct 1.
	  rename x into t.
	  destruct H5.
	  destruct H6.
	  apply conv_trans with (pi M1 C).
	   assumption.
	   apply conv_trans with (pi M1 C').
	    apply conv_pir.
	      apply IHM2 with (Gamma, M1); assumption.
	    apply conv_sym.
	      assumption.
	assumption.
    assumption.
Qed.

Lemma Typing_Lemma_sortlike : forall n (Gamma : context n) M A,
  Gamma |- M ; A -> sortlike M ->
  exists m, exists Delta : string m n, exists s,
  A ->> Pi Delta (srt s).
Proof.
 induction 1; simpl.
(* axioms *)
  split with O.
    split with (emp (m:=O)).
    split with t.
    apply red_ref.
(* start *)
  destruct 1.
(* weakening *)
  intro.
    elim IHPTS1.
     intro m.
       destruct 1.
       rename x into Delta.
       destruct H2.
       rename x into t.
       split with (S m).
       split with (liftstring Delta).
       split with t.
       unfold liftstring.
       change (srt (n:=S m) t) with (subvar (srt t) (subvar_lift (mtch_Sm_Sn m n Delta) (up (n:=n)))).
       rewrite <- Pi_subvar with (rho := up (n:=n)) (B := srt (n:=m) t) (e := mtch_Sm_Sn m n Delta) (Delta := Delta).
       apply red_liftterm with (N := Pi Delta (srt t)).
       assumption.
     apply sortlike_liftterm'.
       assumption.
(* product *)
  intros _.
    split with n.
    split with (emp (m:=n)).
    split with s3.
    apply red_ref.
(* application *)
  intro.
    elim IHPTS1.
     destruct x.
      destruct 1.
        induction x.
         destruct H2.
	   elim not_red_pi_srt with O A B x.
	   assumption.
	 elim le_Sn_O with n.
	   apply string_leq.
	   assumption.
        destruct 1.
	  destruct H2.
	  rename x1 into s.
          induction x0.
	   elim not_red_pi_srt with (S x) A B s.
	     assumption.
	   split with x.
	     split with (subbot_string x0 a).
	     split with s.
	     unfold subbot_string.
	     change (srt (n := x) s) with (subst (srt s) (subst_lift (mtch_Sm_Sn_inv _ _ x0)
	       (fun x : fin (S n) =>
		 match x with
		   Some y => var y |
		     None   => a
		 end))).
	     rewrite <- Pi_subst.
	     apply red_subbot with (M := B) (N := Pi x0 (srt s)) (P := a) (Q := a).
	      apply red_pi_injr with A t.
	        assumption.
	      apply red_ref.
     assumption.
(* abstraction *)
  intro.
    elim IHPTS1.
     intro m.
       destruct 1.
       rename x into Delta.
       destruct H4.
       rename x into s.
       split with m.
       split with (cons A Delta).
       split with s.
       simpl.
       apply red_pir.
       assumption.
     assumption.
(* conversion *)   
  intro.
    elim IHPTS1.
     intro m.
       destruct 1.
       rename x into Delta.
       destruct H3.
       rename x into t.
       split with m.
       elim Church_Rosser with n B B'.
        intro B0.
	  destruct 1.
	  elim red_dmnd with n B (Pi Delta (srt t)) B0; auto.
	  intro B1.
	  destruct 1.
	  elim red_Pi_inv with m n Delta (srt (n:=m) t) B1.
	   intro Delta0.
	     destruct 1.
	     rename x into C.
	     destruct H8.
	     destruct H9.
	     split with Delta0.
	     split with t.
	     apply red_trans with B0.
	      assumption.
	      rewrite <- Gen_red_srt with m t C.
	       rewrite <- H10.
	         assumption.
	       assumption.
	   assumption.
	assumption.
     assumption.
Qed.

Definition Sigma : forall n : nat, (term n) -> (context n) -> sort -> Prop.
  induction 1.
  intros _ _.
    exact False.
  intros _.
    exact (axiom s).
  exact IHterm1.
  intros Gamma s3.
    exact (exists s1 : sort, exists s2 : sort, rule s1 s2 s3 /\
      ((varlike H /\ PTS Gamma H (srt s1)) \/ (sortlike H /\ IHterm1 Gamma s1)) /\
      ((varlike H0 /\ PTS (n := S n) (Gamma, H) H0 (srt s2)) \/ (sortlike H0 /\ IHterm2 (Gamma, H) s2))).
  intro Gamma.
    exact (IHterm2 (Gamma, H)).
Defined.

Implicit Arguments Sigma [n].

Theorem Sigma_ctxt_irrel : forall (m : nat) (a : term m) (n : nat) (A : term m) (Delta : context m) (Gamma : context n) (rho : fin m -> fin n),
  sortlike a -> Delta |- a ; A -> valid Gamma -> subctxt Delta Gamma rho ->
  forall s : sort, Sigma a Delta s <-> Sigma (subvar a rho) Gamma s.
Proof.
 induction a; simpl; intros.
(* var *)
  destruct H.
(* srt *)
  tauto.
(* app *)
  elim Gen_app with n Delta a1 a2 A.
   intro A0.
     destruct 1.
     rename x into B0.
     destruct H3.
     destruct H4.
     apply IHa1 with (pi A0 B0); assumption.
   assumption.
(* pi *)
  elim Gen_pi with n Delta a1 a2 A.
   intro t1.
     destruct 1.
     rename x into t2.
     destruct H3.
     rename x into t3.
     destruct H3.
     destruct H4.
     destruct H5.
     split.
      destruct 1.
        rename x into s1.
	destruct H7.
	rename x into s2.
	destruct H7.
	destruct H8.
	split with s1.
	split with s2.
	assert (Gamma |- subvar a1 rho ; srt t1).
	  apply Weakening with (Delta:=Delta) (rho:=rho) (A:=srt (n:=n) t1); assumption.
	split.
	 assumption.
	split.
	 destruct H8; destruct H8.
	  left.
	    split.
	     apply varlike_subvar.
	       assumption.
	     apply Weakening with (Delta:=Delta) (rho:=rho) (A:=srt (n:=n) s1); assumption.
	  right.
	    split.
	     apply sortlike_subvar.
	       assumption.
	     elim IHa1 with n0 (srt (n:=n) t1) Delta Gamma rho s1; auto.
	 destruct H9; destruct H9.
	  left.
	    split.
	     apply varlike_subvar.
	       assumption.
	     apply Weakening with (n:=S n) (Delta:=(Delta,a1)) (rho:=Sfun rho) (A:=srt (n:=S n) s2).
	      assumption.
	      split with t1.
	        assumption.
	      apply Weak_subctxt.
	        assumption.
          right.
	    split.
	     apply sortlike_subvar.
	       assumption.
	     elim IHa2 with (S n0) (srt (n:=S n) t2) (Delta, a1) (Gamma, subvar a1 rho) (Sfun rho) s2; auto.
	      split with t1.
	        assumption.
              apply Weak_subctxt.
	        assumption.
   destruct 1.
     rename x into s1.
     destruct H7.
     rename x into s2.
     destruct H7.
     destruct H8.
     split with s1.
     split with s2.
     split.
      assumption.
     split.
      destruct H8; destruct H8.
       left.
        split.
	 apply varlike_subvar' with n0 rho.
	   assumption.
	 replace s1 with t1.
	  assumption.
	  apply conv_srt_inj with n0.
	    apply Unique_Type_varlike with (subvar a1 rho) Gamma; try assumption.
	    apply Weakening with (Delta:=Delta) (A:=srt (n:=n) t1) (rho:=rho); assumption.
       right.
        assert (Is_true (sortlike a1)).
	  apply sortlike_subvar' with n0 rho.
	  assumption.
        split.
	 assumption.
	 elim IHa1 with n0 (srt (n:=n) t1) Delta Gamma rho s1; auto.
      destruct H9; destruct H9.
       left.
        split.
	 apply varlike_subvar' with (S n0) (Sfun rho).
	   assumption.
	 replace s2 with t2.
	  assumption.
	  apply conv_srt_inj with (S n0).
	    apply Unique_Type_varlike with (subvar a2 (Sfun rho)) (Gamma, subvar a1 rho); auto.
	    apply Weakening with (n:=S n) (Delta := (Delta, a1)) (A := srt (n:=S n) t2) (rho := Sfun rho).
	     assumption.
	     apply Context_Validity with (subvar a2 (Sfun rho)) (srt (n:=S n0) s2).
	       assumption.
	     apply Weak_subctxt.
	       assumption.
       right.
        assert (Is_true (sortlike a2)).
	  apply sortlike_subvar' with (S n0) (Sfun rho).
	  assumption.
        split.
	 assumption.
	 elim IHa2 with (S n0) (srt (n:=S n) t2) (Delta, a1) (Gamma, subvar a1 rho) (Sfun rho) s2; auto.
	  split with t1.
	    apply Weakening with (Delta:=Delta) (A:=srt (n:=n) t1) (rho:=rho); auto.
	    apply Weak_subctxt.
	    assumption.
   assumption.
(* lda *)
  elim Gen_lda with n Delta a1 a2 A.
   intro B.
     destruct 1.
     rename x into t.
     destruct H3.
     destruct H4.
     apply IHa2 with B; try assumption.
      elim (Context_Validity (S n) (Delta, a1) a2 B).
       intro t'.
	 split with t'.
	 apply Weakening with (Delta:=Delta) (A:=srt (n:=n) t') (rho:=rho); assumption.
       assumption.
      apply Weak_subctxt.
        assumption.
   assumption.
Qed.

Theorem pre_Sigma_typing : forall n (Gamma : context n) a A,
  Gamma |- a ; A ->
  forall m (Delta : string m n) s1 s,
  sortlike a -> red A (Pi Delta (srt s1)) -> Sigma a Gamma s ->
  exists Theta, exists a1 : term m,
  red a (Lda Theta a1) /\ PTS (concat Gamma Theta) a1 (srt s).
Proof.
 induction 1; simpl.
(* axioms *)
  destruct m.
   intro Delta.
     rewrite string_n_n with O Delta.
     intros s1 s' _ H0 H1.
     split with (emp (m:=O)).
     split with (srt (n:=O) s).
     simpl.
     split.
      apply red_ref.
      apply axioms.
        assumption.
   intro Delta.
     rewrite string_m_n with (S m) O Delta (lt_O_Sn m).
     simpl.
     intros s1 s' _ H0.
     elim not_red_srt_pi with O t (head Delta (lt_O_Sn m)) (Pi (tail Delta (lt_O_Sn m)) (srt s1)).
     assumption.
(* start *)
  destruct 1.
(* weak *)
  destruct m.
   intro Delta.
     elim le_Sn_O with n.
     apply string_leq.
     assumption.
   intros Delta s1 s2 H1 H2 H3.
     elim red_subvar_Pi with m (S m) n (S n) (mtch_Sm_Sn' _ _ Delta) B (up (n:=n)) Delta (srt (n := S m) s1).
      intro Delta'.
        destruct 1.
        rename x into C'.
        destruct H4.
        destruct H5.
	assert (Is_true (sortlike A)).
	  apply sortlike_liftterm'.
	  assumption.
        elim IHPTS1 with m Delta' s1 s2.
         intro Theta.
           destruct 1.
	   rename x into a1.
	   destruct H8.
	   split with (liftstring Theta).
	   split with (subvar a1 (subvar_lift (mtch_Sm_Sn _ _ Theta) (up (n:=n)))).
	   unfold liftstring.
	   split.
	    rewrite <- Lda_subvar with m (S m) n (S n) (mtch_Sm_Sn _ _ Theta) Theta a1 (up (n:=n)).
	      apply red_liftterm with (n:=n) (M:=A) (N:=Lda Theta a1).
	      assumption.
	    apply Weakening with (Delta := Gamma @ Theta) (A := srt (n:=m) s2) (rho := subvar_lift (mtch_Sm_Sn _ _ Theta) (up (n:=n))).
	     assumption.
	     apply valid_concat with Gamma.
	       split.
	        apply Context_Validity with a1 (srt (n:=m) s2).
	          assumption.
	        split with s.
	          assumption.
	     apply subctxt_concat.
	       unfold subctxt.
	       reflexivity.
         assumption.
         rewrite <- subvar_srt with m C' (S m) (subvar_lift (mtch_Sm_Sn' _ _ Delta) (up (n:=n))) s1; auto.
	 elim Sigma_ctxt_irrel with n A (S n) B Gamma (Gamma, C) (up (n:=n)) s2; try assumption.
          intros.
            apply H9.
	    assumption.
	  split with s.
            assumption.
          unfold subctxt.
            reflexivity.
      assumption.
(* product *)
  induction Delta.
   intros s4 s _ _.
     clear s4.
     destruct 1.
     rename x into t1.
     destruct H2.
     rename x into t2.
     destruct H2.
     destruct H3.
     split with (emp (m:=m)).
     destruct H3; destruct H3; destruct H4; destruct H4.
      split with (pi A B).
        split.
	 apply red_ref.
	 apply product with t1 t2; assumption.
      elim IHPTS2 with (m0 := S m) (Delta := emp (m:=S m)) (s1 := s2) (s := t2); auto.
        intro Theta.
        rewrite string_n_n with (S m) Theta.
	destruct 1.
	rename x into B1.
	destruct H7.
	split with (pi A B1).
	split.
	 apply red_pir with (A := A) (B' := B1).
	   assumption.
	 apply product with t1 t2; auto.
      elim (IHPTS1 m emp s1 t1); auto.
        intro x.
	rewrite string_n_n with m x.
	clear x.
	simpl.
	destruct 1.
	rename x into A0.
	destruct H7.
	split with (pi A0 B).
	split.
	 apply red_pil.
	   assumption.
	 apply product with t1 t2; try assumption.
	   apply Context_Conversion with (Gamma, A).
	    assumption.
	    apply conv_ctxt_build.
	     apply conv_ctxt_ref.
	     apply conv_red.
	       assumption.
	    split with t1.
	      assumption.
      simpl.
        elim IHPTS1 with m (emp (m:=m)) s1 t1; auto.
	intro x.
	rewrite string_n_n with m x.
	clear x.
	simpl.
	destruct 1.
	rename x into A0.
	destruct H7.
	elim IHPTS2 with (S m) (emp (m:=S m)) s2 t2; auto.
	intro x.
	rewrite string_n_n with (S m) x.
	clear x.
	simpl.
	destruct 1.
	rename x into B0.
	destruct H9.
	split with (pi A0 B0).
	split.
	 apply red_pi; assumption.
	 apply product with t1 t2; try assumption.
	  apply Context_Conversion with (Gamma, A).
	   assumption.
	   apply conv_ctxt_build.
	    apply conv_ctxt_ref.
	    apply conv_red.
	      assumption.
	   split with t1.
	     assumption.
(* abstraction *)
  intros s4 s _ H2.
    simpl in H2.
    elim not_red_srt_pi with n s3 t (Pi Delta (srt s4)).
    assumption.
(* application *)
  intros.
    elim Typing_Lemma_sortlike with n Gamma F (pi A B); try assumption.
    intro p.
    case (lt_eq_lt_dec p n).
    destruct 1.
     destruct 1.
       elim le_not_lt with n p.
        apply string_leq.
          assumption.
	assumption.
     rewrite e.
       clear p e.
       destruct 1.
       rewrite string_n_n with n x in H4.
       clear x.
       destruct H4.
       rename x into s'.
       elim not_red_pi_srt with n A B s'.
       assumption.
     case p.
      intro.
        elim lt_n_O with n.
	assumption.
      clear p.
        intros p n_lt_Sp.
	destruct 1.
	rename x into Theta.
	destruct H4.
	rename x into s1'.
	rewrite string_m_n with (S p) n Theta n_lt_Sp in H4.
	simpl in H4.
	assert (m = p).
	  apply conv_Pi_srt with n Delta (subbot_string (tail Theta n_lt_Sp) a) s1 s1'.
	  apply conv_trans with (subbot B a).
	   apply conv_sym.
	     apply conv_red.
	     assumption.
	   apply conv_red.
	     change (srt (n:=p) s1') with (subst (srt (n:=S p) s1') (subst_lift (mtch_Sm_Sn_inv _ _ (tail Theta n_lt_Sp))
	       (botsub a))).
	     unfold subbot_string.
	     rewrite <- Pi_subst.
	     unfold subbot.
	     apply red_substl.
	     apply red_pi_injr with A (head Theta n_lt_Sp).
	     assumption.
        generalize H2.
	clear H2.
	generalize Delta.
	clear Delta.
	rewrite H5.
	clear m H5.
	intros.
	elim IHPTS1 with (S p) Theta s1' s; try assumption.
         intro Phi.
	   destruct 1.
	   rename x into a1.
 	   destruct H5.
	   split with (subbot_string (tail Phi n_lt_Sp) a).
	   split with (subst a1 (subst_lift (mtch_Sm_Sn_inv _ _ (tail Phi n_lt_Sp)) (botsub a))).
	   split.
	    unfold subbot_string.
	      rewrite <- Lda_subst.
	      apply red_trans with (app (Lda Phi a1) a).
	       apply red_appl.
	         assumption.
	       rewrite string_m_n with (S p) n Phi n_lt_Sp.
	         simpl.
	         apply red_beta with (n:=n) (A:=head Phi n_lt_Sp) (M:=Lda (tail Phi n_lt_Sp) a1) (N:=a).
	    change (srt (n:=p) s) with (subst (srt s) (subst_lift (mtch_Sm_Sn_inv _ _ (tail Phi n_lt_Sp)) (botsub a))).
	      elim Gen_lda' with n Gamma (head Phi n_lt_Sp) (Lda (tail Phi n_lt_Sp) a1) (pi A B); auto.
               intro C.
	         destruct 1.
		 rename x into t1.
		 destruct H7.
		 rename x into t2.
		 destruct H7.
		 rename x into t3.
		 destruct H7.
		 destruct H8.
		 destruct H9.
		 destruct H10.
		 assert (Gamma |= botsub a ; (Gamma, head Phi n_lt_Sp)).
		   apply satisfy_botsub.
		   apply conversion with A t1; try assumption.
		   apply conv_pi_injl with B C.
		   assumption.
		 assert (valid (((Gamma, head Phi n_lt_Sp) : context (S n)) @ tail Phi n_lt_Sp)).
		   rewrite string_m_n with (S p) n Phi n_lt_Sp in H6.
		   apply Context_Validity with a1 (srt (n:=S p) s).
		   assumption.
		 assert (valid Gamma).
		   apply Context_Validity with a A.
		   assumption.
                 apply Substitution with (concat Gamma Phi); auto.
		  unfold subbot_string.
		    apply valid_concat' with (Gamma, head Phi n_lt_Sp); assumption.
		  unfold subbot_string.
		    rewrite string_m_n with (S p) n Phi n_lt_Sp.
		    simpl.
		    apply satisfy_concat; assumption.
               rewrite string_m_n with (S p) n Phi n_lt_Sp in H5.
	         simpl in H5.
		 apply Subject_Reduction with F; assumption.
         rewrite string_m_n with (S p) n Theta n_lt_Sp.
	   exact H4.
(* abstraction *)
  intro m.
    case (lt_eq_lt_dec m n).
    destruct 1.
     intro Delta.
       elim lt_not_le with m n.
        assumption.
	apply string_leq.
	  assumption.
     rewrite e.
       clear m e.
       intro Delta.
       rewrite string_n_n with n Delta.
       clear Delta.
       simpl.
       intros s4 s H3 H4.
       elim not_red_pi_srt with n A B s4.
       assumption.
     intros.
       rewrite string_m_n with m n Delta l in H4.
       simpl in H4.
       elim IHPTS1 with m (tail Delta l) s0 s; try assumption.
        intro Theta.
          destruct 1.
	  rename x into b1.
	  destruct H6.
	  split with (cons A Theta).
	  split with b1.
	  simpl.
	  split.
           apply red_ldar.
	     assumption.
	   assumption.
	apply red_pi_injr with A (head Delta l).
	  assumption.
(* conversion *)
  intros.
    elim Church_Rosser with n B (Pi Delta (srt s1)).
     intro B0.
       destruct 1.
       elim red_Pi_inv with m n Delta (srt (n:=m) s1) B0.
        intro Delta0.
          destruct 1.
	  rename x into C.
	  destruct H7.
	  destruct H8.
	  apply IHPTS1 with Delta0 s1; try assumption.
	  rewrite <- Gen_red_srt with m s1 C.
	   rewrite <- H9.
	     assumption.
	   assumption.
	assumption.
     apply conv_trans with B'.
      assumption.
      apply conv_red.
        assumption.
Qed.

Theorem Sigma_typing : forall n (Gamma : context n) A s1 s2,
  sortlike A -> Gamma |- A ; srt s1 -> Sigma A Gamma s2 ->
  exists A', A ->> A' /\ Gamma |- A' ; srt s2.
Proof.
 intros.
 elim pre_Sigma_typing with n Gamma A (srt (n:=n) s1) n (emp (m:=n)) s1 s2; auto.
 intro Delta.
 rewrite string_n_n with n Delta.
 trivial.
Qed.

Lemma pre_Sigma_gen : forall n (Gamma : context n) M A, Gamma |- M ; A ->
  forall m (Theta : string m n) s, sortlike M -> A ->> Pi Theta (srt s) ->
  Sigma M Gamma s.
Proof.
 induction 1; simpl.
(* axioms *)
  destruct m; intro Theta.
   rewrite string_n_n with O Theta.
     intros s' _ H0.
     rewrite srt_inj with O s' t.
      assumption.
      apply Gen_red_srt.
        assumption.
   rewrite string_m_n with (S m) O Theta (lt_O_Sn m).
     simpl.
     intros s' _ H0.
     elim not_red_srt_pi with O t (head Theta (lt_O_Sn m)) (Pi (tail Theta (lt_O_Sn m)) (srt s')).
     assumption.
(* start *)
  destruct 1.
(* weakening *)
  destruct m.
   intro Theta.
     elim lt_not_le with O (S n).
      apply lt_O_Sn.
      apply string_leq.
        assumption.
   intros Theta s' H1 H2.
     assert (Is_true (sortlike A)).
       apply sortlike_liftterm'.
       assumption.
     elim Sigma_ctxt_irrel with n A (S n) B Gamma (Gamma, C) (up (n:=n)) s'; try assumption.
      intros.
        apply H4.
	unfold liftterm in H3.
	elim red_subvar_Pi with m (S m) n (S n) (mtch_Sm_Sn' _ _ Theta) B (up (n:=n)) Theta (srt (n:=S m) s').
	 intro Theta0.
	   destruct 1.
	   rename x into M.
	   destruct H6.
	   destruct H7.
	   apply IHPTS1 with m Theta0.
	    assumption.
	    rewrite <- subvar_srt with m M (S m) (subvar_lift (mtch_Sm_Sn' m n Theta) (up (n:=n))) s'.
	     assumption.
	     symmetry.
	       assumption.
	 assumption.
      split with s.
        assumption.
      apply Weak_subctxtr with (rho := id (fin n)).
        apply Triv_subctxt.
(* product *)      
  intro m.
    case (lt_eq_lt_dec m n).
    destruct 1.
     intro Theta.
       elim lt_not_le with m n.
        assumption.
        apply string_leq.
          assumption.
     rewrite e.
       clear m e.
       intro Theta.
       rewrite string_n_n with n Theta.
       clear Theta.
       simpl.
       intros s _ H2.
       rewrite <- red_srt_inj with n s3 s.
        clear s H2.
	  split with s1.
	  split with s2.
	  split.
	   assumption.
	  split.
	   elim var_or_sort with n A.
	    auto.
	    right.
	      split.
	       assumption.
	       apply IHPTS1 with n (emp (m:=n)); auto.
	   elim var_or_sort with (S n) B.
	    auto.
	    right.
	      split.
	       assumption.
	       apply IHPTS2 with (S n) (emp (m:=S n)); auto.
        assumption.
     intros n_lt_m Theta.
       rewrite string_m_n with m n Theta n_lt_m.
       simpl.
       intros s _ H2.
       elim not_red_srt_pi with n s3 (head Theta n_lt_m) (Pi (tail Theta n_lt_m) (srt s)).
       assumption.
(* application *)
  intros.
    elim Typing_Lemma_sortlike with n Gamma F (pi A B); try assumption.
    destruct x.
     destruct 1.
       rename x into Phi.
       case (lt_eq_lt_dec O n).
       destruct 1.
	elim lt_not_le with O n.
	 assumption.
	 apply string_leq.
	   assumption.
	generalize H3.
	  generalize B.
	  generalize A.
	  generalize Phi.
	  rewrite e.
	  intro Phi'.
	  rewrite string_n_n with n Phi'.
	  destruct 1.
	  elim not_red_pi_srt with n A0 B0 x.
	  assumption.
	intro.
	  elim lt_n_O with n.
	  assumption.
    rename x into p.
      destruct 1.
      rename x into Delta.
      destruct H3.
      rename x into t.
      elim (lt_eq_lt_dec (S p) n).
      destruct 1.
       elim lt_not_le with (S p) n.
        assumption.
	apply string_leq.
	  assumption.
       generalize H3.
	 generalize B.
	 generalize A.
	 generalize Delta.
	 rewrite e.
	 intro Delta'.
	 rewrite string_n_n with n Delta'.
	 intros.
	 elim not_red_pi_srt with n A0 B0 t.
	 assumption.
       intro n_lt_Sp.
	 apply IHPTS1 with (S p) Delta.
	  assumption.
	  rewrite conv_Pi_srt' with m n Theta p (subbot_string (tail Delta n_lt_Sp) a) s t.
	   assumption.
	   apply conv_trans with (subbot B a).
	    apply conv_red'.
	      assumption.
	    apply conv_red.
	      rewrite <- Pi_subbot_srt.
	      apply red_subbotl.
	      rewrite string_m_n with (S p) n Delta n_lt_Sp in H3.
	      apply red_pi_injr with A (head Delta n_lt_Sp).
	      assumption.
(* abstraction *)
  intro m.
    case (lt_eq_lt_dec m n).
    destruct 1.
     intro Theta.
       elim (lt_not_le m n).
        assumption.
	apply string_leq.
          assumption.
     rewrite e.
       clear m e.
       intro Theta.
       rewrite string_n_n with n Theta.
       clear Theta.
       intros.
       elim not_red_pi_srt with n A B s.
       assumption.
     intros n_lt_m Theta.
       rewrite string_m_n with m n Theta n_lt_m.
       intros.
       apply IHPTS1 with m (tail Theta n_lt_m).
        assumption.
	apply red_pi_injr with A (head Theta n_lt_m).
	  assumption.
(* conversion *)
  intros.
    elim Church_Rosser with n B (Pi Theta (srt s0)).
     intro B0.
       destruct 1.
       elim red_Pi_inv with m n Theta (srt (n:=m) s0) B0.
        intro Theta0.
          destruct 1.
	  rename x into A'.
	  destruct H6.
	  destruct H7.
	  apply IHPTS1 with m Theta0; try assumption.
	  rewrite H8 in H4.
	  rewrite <- Gen_red_srt with m s0 A'; assumption.
	assumption.
     apply conv_trans with B'.
      assumption.
      apply conv_red.
        assumption.
Qed.

Theorem Sigma_gen : forall n (Gamma : context n) a s,
  sortlike a -> Gamma |- a ; srt s -> Sigma a Gamma s.
Proof.
  intros.
  apply pre_Sigma_gen with (srt (n := n) s) n (emp (m:=n)); auto.
Qed.

Lemma pre_Strengthening : forall n b (Gamma : context n) B,
  Gamma |- b ; B ->
  forall m (Delta : context m) rho b0,
  valid Delta ->
  injective rho ->
  subctxt Delta Gamma rho ->
  b = subvar b0 rho ->
  exists B', B ->> subvar B' rho /\ Delta |- b0 ; B'.
Proof.
  induction b; intros.
(* var *)
   elim subvar_var with m b0 n rho f.
    intro x.
      destruct 1.
      rewrite H4.
      clear b0 H3 H4.
      rewrite H5 in H.
      clear f H5.
      assert (typeof (rho x) Gamma ~= B).
        apply Gen_var.
        assumption.
      elim Church_Rosser with n (typeof (rho x) Gamma) B.
       intro B'.
         destruct 1.
	 rewrite H2 in H4.
	 elim red_subvar_inv with m n (typeof x Delta) rho B'.
	  intro B1.
	    destruct 1.
	    rewrite H7 in H5.
	    clear H7.
	    split with B1.
	    split.
	     assumption.
	     apply Predicate_Reduction with (typeof x Delta).
	      apply Start_var.
	        assumption.
	      assumption.
	  assumption.
       assumption.
    symmetry.
      assumption.
(* srt *)
   rewrite subvar_srt with m b0 n rho s.
    elim Gen_srt with n Gamma s B.
     intro t.
       destruct 1.
       split with (srt (n:=m) t); simpl.
       split.
        assumption.
	apply Start_ax; assumption.
     assumption.
    symmetry.
      assumption.
(* app *)
   elim subvar_app with m b0 n rho b1 b2; auto.
   clear H3.
   intro M.
   destruct 1.
   rename x into N.
   destruct H3.
   destruct H4.
   rewrite H3.
   clear b0 H3.
   elim Gen_app with n Gamma b1 b2 B; auto.
   intro A.
   destruct 1.
   rename x into C.
   destruct H3.
   destruct H6.
   elim IHb1 with Gamma (pi A C) m Delta rho M; auto.
   intro X.
   destruct 1.
   elim IHb2 with Gamma A m Delta rho N; auto.
   intro A'.
   destruct 1.
   elim Gen_red_pi with n A C (subvar X rho); auto.
   intro A0.
   destruct 1.
   rename x into C0.
   destruct H12.
   destruct H13.
   elim subvar_pi with m X n rho A0 C0; auto.
   intro A1.
   destruct 1.
   rename x into B1.
   destruct H15.
   destruct H16.
   assert (A1 ~= A').
     apply conv_subvar_inj with n rho.
      assumption.
      apply conv_trans with A.
       apply conv_red'.
         rewrite H16.
	 assumption.
       apply conv_red.
         assumption.
   elim Church_Rosser with m A1 A'; auto.
   intro A00.
   destruct 1.
   assert (Delta |- app M N ; subbot B1 N).
     apply application with A00.
      apply Predicate_Reduction with X.
       assumption.
       rewrite H15.
         apply red_pil.
	 assumption.
      apply Predicate_Reduction with A'; assumption.
   elim Church_Rosser with n (subvar (subbot B1 N) rho) B.
    intro Y.
      destruct 1.
      elim red_subvar_inv with m n (subbot B1 N) rho Y; auto.
      intro B'.
      destruct 1.
      split with B'.
      split.
       rewrite <- H25.
         assumption.
       apply Predicate_Reduction with (subbot B1 N); assumption.
    rewrite subvar_subbot.
      rewrite H17.
      rewrite H5.
      apply conv_trans with (subbot C b2).
       apply conv_subbotl.
         apply conv_red'.
	 assumption.
       apply conv_sym.
         assumption.
(* pi *)
   elim Gen_pi with n Gamma b1 b2 B; auto.
   intro s1.
   destruct 1.
   rename x into s2.
   destruct H4.
   rename x into s3.
   destruct H4.
   destruct H5.
   destruct H6.
   split with (srt (n:=m) s3).
   split; auto.
   elim subvar_pi with m b0 n rho b1 b2; auto.
   intro A.
   destruct 1.
   rename x into C.
   destruct H8.
   destruct H9.
   rewrite H8.
   clear b0 H8 H3.
   elim IHb1 with Gamma (srt (n:=n) s1) m Delta rho A; auto.
   intro X.
   destruct 1.
   replace X with (srt (n:=m) s1) in H8.
    elim IHb2 with (Gamma, b1) (srt (n:=S n) s2) (S m) (Delta, A) (Sfun rho) C; auto.
     intro Y.
       destruct 1.
       replace Y with (srt (n:=S m) s2) in H12.
        apply product with s1 s2; assumption.
        symmetry.
	  apply subvar_srt with (S n) (Sfun rho).
	  apply Gen_red_srt.
	  assumption.
     split with s1.
       assumption.
     apply Sfun_inj.
       assumption.
     rewrite <- H9.
       apply Weak_subctxt.
       assumption.
    symmetry.
      apply subvar_srt with n rho.
      apply Gen_red_srt.
      assumption.
(* lda *)
   rename b1 into B'.
   rename b2 into c.
   rename b0 into L.
   rename B into P.
   elim Gen_lda' with n Gamma B' c P; auto.
   intro C.
   destruct 1.
   rename x into s1.
   destruct H4.
   rename x into s2.
   destruct H4.
   rename x into s3.
   destruct H4.
   destruct H5.
   destruct H6.
   destruct H7.
   elim Gen_conv_pi with n B' C P; try (apply conv_sym; assumption).
   intro B'0.
   destruct 1.
   rename x into C0.
   destruct H9.
   destruct H10.
   elim subvar_lda with m L n rho B' c; auto.
   intro B'low.
   destruct 1.
   rename x into clow.
   destruct H12.
   destruct H13.
   elim IHb1 with Gamma (srt (n:=n) s1) m Delta rho B'low; auto.
   intro s1low.
   destruct 1.
   rewrite subvar_srt with m s1low n rho s1 in H16.
    clear H15 s1low.
      elim IHb2 with (Gamma, B') C0 (S m) (Delta, B'low) (Sfun rho) clow; auto.
       intro C'low.
         destruct 1.
	 elim red_subvar_inv with m n B'low rho B'0.
	  intro B'0low.
	    destruct 1.
	    elim Type_Validity with (S m) (Delta, B'low) clow C'low; auto; destruct 1.
	    (* Case One: C'low is a sort *)
	     rename x into s2'.
	     rewrite H20 in H15.
	     split with (pi B'0low (srt s2')).
	     split.
	      apply red_trans with (pi B'0 C0).
	       assumption.
	       rewrite H19.
	         simpl.
		 apply red_pir.
		 assumption.
	      rewrite H12.
	        apply Predicate_Reduction with (pi B'low (srt s2')).
		 apply abstraction with s1 s2 s3; auto.
		  rewrite <- H20.
		    assumption.
		  apply Start_ax.
		   apply Gen_srt' with (S n) (Gamma, B').
		     apply Subject_Reduction with C.
		      assumption.
		      apply red_trans with C0; assumption.
		 split with s1.
		   assumption.
		 apply red_pil.
		   assumption.
	   (* Case two : C'low : s2 *)
           rename x into s2'.
	   elim var_or_sort with (S m) C'low.
	   (* Case 2.1 : C'low is varlike *)
	    split with (pi B'0low C'low).
	    split.
	     apply red_trans with (pi B'0 C0).
	      assumption.
	      rewrite H19.
	        simpl.
	        apply red_pir.
	        assumption.
	     rewrite H12.
	       apply Predicate_Reduction with (pi B'low C'low).
	        apply abstraction with s1 s2 s3; auto.
		  replace s2 with s2'.
		   assumption.
		   apply conv_srt_inj with (S n).
		     apply Unique_Type_varlike with (subvar C'low (Sfun rho)) (Gamma, B').
		      apply varlike_subvar.
		        assumption.
		      apply Weakening with (n:=S m) (Delta:=(Delta, B'low)) (M:=C'low) (A:=srt (n:=S m) s2') (m:=S n) (Gamma:=(Gamma,B')) (rho:=Sfun rho); auto.
		       apply Context_Validity with c C.
		         assumption.
		       rewrite <- H13.
		         apply Weak_subctxt.
			 assumption.
		      apply Subject_Reduction with C.
		       assumption.
		       apply red_trans with C0; auto.
	        apply red_pil.
		  assumption.
	   (* Case 2.2 : C'low is sortlike *)
            intro.
	    elim Sigma_typing with (S m) (Delta, B'low) C'low s2' s2; auto.
	     intro C''low.
	       destruct 1.
	       split with (pi B'0low C''low).
	       split.
	        apply red_trans with (pi B'0 C0).
		 assumption.
		 simpl.
	           rewrite H19.
		   apply red_pir.
		   apply red_trans with (subvar C'low (Sfun rho)).
		    assumption.
		    apply red_subvar.
		      assumption.
		rewrite H12.
		  apply Predicate_Reduction with (pi B'low C''low).
		   apply abstraction with s1 s2 s3; auto.
		     apply Predicate_Reduction with C'low; auto.
		   apply red_pil.
		     assumption.
	     elim Sigma_ctxt_irrel with (S m) C'low (S n) (srt (n:=S m) s2') (Delta, B'low) (Gamma, B') (Sfun rho) s2; auto.
	      intros.
	        apply H23.
		apply Sigma_gen.
	         apply sortlike_subvar.
		   assumption.
		 apply Subject_Reduction with C; auto.
		   apply red_trans with C0; auto.
	      split with s1.
	        assumption.
              rewrite <- H13.
	        apply Weak_subctxt.
		assumption.
	  rewrite H13.
	    assumption.
      apply Predicate_Reduction with C; auto.
      split with s1.
        assumption.
      apply Sfun_inj.
        assumption.
      rewrite <- H13.
        apply Weak_subctxt.
	assumption.
    apply Gen_red_srt.
      assumption.
Qed.

Theorem Strengthening : forall m n Delta Gamma M A (rho : fin m -> fin n),
  Gamma |- subvar M rho ; subvar A rho ->
  subctxt Delta Gamma rho ->
  injective rho ->
  valid Delta ->
  Delta |- M ; A.
Proof.
  intros.
  elim pre_Strengthening with n (subvar M rho) Gamma (subvar A rho) m Delta rho M; auto.
  intro A'.
  destruct 1.
  elim Type_Validity with n Gamma (subvar M rho) (subvar A rho); auto; destruct 1; rename x into s.
  (* Case One - A is a sort *)
   replace A with (srt (n:=m) s).
    replace A' with (srt (n:=m) s) in H4.
     assumption.
     symmetry.
       apply subvar_srt with n rho.
       apply Gen_red_srt.
       rewrite <- H5.
       assumption.
    symmetry.
      apply subvar_srt with n rho.
      assumption.
  (* Case Two - A : s *)
   elim pre_Strengthening with n (subvar A rho) Gamma (srt (n:=n) s) m Delta rho A; auto.
     intro X.
     destruct 1.
     apply conversion with A' s; auto.
      apply conv_red'.
        apply red_subvar_inj with n rho; assumption.
      replace (srt (n:=m) s) with X.
       assumption.
       apply subvar_srt with n rho.
         apply Gen_red_srt.
	 assumption.
Qed.
