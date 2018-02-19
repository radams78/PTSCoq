Require Export PTS.
Require Import CR.

Lemma Context_Strength : forall (n : nat) (Gamma : context n) (A : term n),
  valid (n:=S n) (Gamma, A) -> valid Gamma.
Proof.
simpl.
destruct 1.
rename x into s.
apply Context_Validity with A (srt (n:=n) s).
assumption.
Qed.

Theorem Weakening : forall (n : nat) (Delta : context n) (M A : term n),
  Delta |- M ; A ->
  forall (m : nat) (Gamma : context m) (rho : fin n -> fin m),
  valid Gamma ->
  subctxt Delta Gamma rho ->
  Gamma |- subvar M rho ; subvar A rho.
Proof.
induction 1; simpl; intros.
(* axioms *)
apply Start_ax; assumption.
(* start *)
replace (subvar (liftterm A) rho) with (typeof (rho bot) Gamma0).
 apply Start_var.
   assumption. 
 apply H1 with (x := bot (n:=n)).
(* weakening *)
repeat rewrite subvar_liftterm.
  apply IHPTS1.
  assumption.
  apply Strength_subctxt with C.
  assumption.
(* product *)
assert (Gamma0 |- subvar A rho ; srt s1).
   apply IHPTS1 with (rho := rho); assumption.
  apply product with s1 s2; auto.
  apply IHPTS2 with (rho := Sfun rho).
   split with s1.
     assumption.
   apply Weak_subctxt.
     assumption.
(* application *)
rewrite subvar_subbot.
  apply application with (subvar A rho).
   apply IHPTS1 with (rho := rho); assumption.
   apply IHPTS2; assumption.
(* abstraction *)
assert (Gamma0 |- subvar A rho ; srt s1).
   apply IHPTS2 with (rho := rho); assumption.
  apply abstraction with s1 s2 s3; auto.
   apply IHPTS1.
    split with s1.
      assumption.
    apply Weak_subctxt.
      assumption.
   apply IHPTS3 with (rho := Sfun rho).
    split with s1.
      assumption.
    apply Weak_subctxt.
      assumption.
(* conversion *)
apply conversion with (subvar B rho) s.
 apply conv_subvar.
   assumption.
 apply IHPTS1; assumption.
 apply IHPTS2 with (rho := rho); assumption.
Qed.

Theorem Substitution : forall n : nat, forall Delta : context n, forall M A : term n, 
  Delta |- M ; A ->
  forall m : nat, forall Gamma : context m, forall sigma : fin n -> term m,
  valid Gamma -> Gamma |= sigma ; Delta -> Gamma |- subst M sigma ; subst A sigma.
Proof.
induction 1; simpl; intros.
(* axioms *)
apply Start_ax; assumption.
(* start *)
apply H1 with (x := bot (n:=n)).
(* weakening *)
repeat rewrite subst_liftterm.
  apply IHPTS1.
   assumption.
   apply Strength_satisfy with C.
     assumption.
(* product *)
assert (Gamma0 |- subst A sigma ; srt s1).
    apply IHPTS1 with (sigma := sigma); assumption.
  apply product with s1 s2; auto.
  apply IHPTS2 with (sigma := liftsub sigma).
   split with s1.
     assumption.
   unfold satisfy.
     destruct x; simpl; rewrite <- liftterm_subst' with (sigma := sigma).
      apply weakening with s1; auto.
      apply start with s1.
        assumption.
(* application *)
rewrite subst_subbot.
  apply application with (subst A sigma).
   apply IHPTS1 with (sigma := sigma); assumption.
   apply IHPTS2; assumption.
(* abstraction *)
assert (Gamma0 |- subst A sigma ; srt s1).
    apply IHPTS2 with (sigma := sigma); assumption.
  assert (((Gamma0, subst A sigma) : context (S m)) |= liftsub sigma ; (Gamma, A)).
    unfold satisfy.
      destruct x; simpl; rewrite <- liftterm_subst' with (sigma := sigma).
       apply weakening with s1; auto.
       apply start with s1.
         assumption.     
  apply abstraction with s1 s2 s3.
   assumption.
   apply IHPTS1.
    split with s1.
      assumption.
    assumption.
   assumption.
   apply IHPTS3 with (sigma := liftsub sigma).
    split with s1.
      assumption.
    assumption.
(* conversion *)
apply conversion with (subst B sigma) s.
 apply conv_subst; auto.
 apply IHPTS1; assumption.
 apply IHPTS2 with (sigma := sigma); assumption.
Qed.

Lemma Weak_satisfy : forall m n (Delta : context m) (Gamma : context n) (sigma : fin m -> term n) (A : term m) (s : sort),
  Gamma |= sigma ; Delta -> Delta |- A ; srt s -> valid Gamma ->
  ((Gamma, subst A sigma) : context (S n)) |= liftsub sigma ; (Delta, A).
Proof.
unfold satisfy at 2.
intros.
assert (Gamma |- subst A sigma ; srt s).
  apply Substitution with (Delta := Delta) (sigma := sigma) (A := srt (n:=m) s); auto.
destruct x; simpl.
 fold fin in f.
   rename f into x.
   rewrite <- liftterm_subst'.
   apply weakening with s; auto.
 rewrite <- liftterm_subst'.
   apply start with s.
   assumption.
Qed.

Lemma Substitution_bot : forall n (Gamma : context n) A N M B,
  Gamma |- N ; A -> ((Gamma, A) : context (S n)) |- M ; B ->
  Gamma |- subbot M N ; subbot B N.
Proof.
intros.
unfold subbot.
assert (valid Gamma).
  apply Context_Validity with N A.
  assumption.
apply Substitution with (Gamma, A); auto.
unfold satisfy.
destruct x; simpl; rewrite subst_liftterm_botsub.
 apply Start_var.
   assumption.
 assumption.
Qed.
 
Lemma pre_Gen_srt : forall n (Gamma : context n) M C,
  Gamma |- M ; C -> forall s, M = srt s -> exists t : sort, C ->> srt t /\ axiom s t.
Proof.
induction 1; try discriminate 1.
(* axioms *)
injection 1.
  split with t.
  rewrite <- H1.
  split; auto.
(* weakening *)
intros.
  elim IHPTS1 with s0.
   destruct 1.
     rename x into t.
     split with t.
     split.
      apply red_liftterm with (N := srt (n:=n) t).
        assumption.
      assumption.
   apply liftterm_inj.
     assumption.
intuition.
(* conversion *)
intros.
  elim IHPTS1 with s0.
   destruct 1.
     split with x.
     split.
      apply Gen_conv_srt.
        apply conv_trans with B.
         apply conv_sym.
           assumption.
         apply conv_red.
           assumption.
      assumption.
   assumption.
Qed.

Theorem Gen_srt : forall n (Gamma : context n) c C,
  Gamma |- srt c ; C -> exists t, C ->> srt t /\ axiom c t.
Proof.
  intros.
  apply pre_Gen_srt with Gamma (srt (n := n) c); auto.
Qed.

Lemma Gen_srt' : forall n (Gamma : context n) c s,
  Gamma |- srt c ; srt s -> axiom c s.
Proof.
  intros.
  elim Gen_srt with n Gamma c (srt (n:=n) s).
   destruct 1.
     rewrite srt_inj with n s x.
      assumption.
      symmetry.
        apply Gen_red_srt.
        assumption.
  assumption.
Save.

Lemma pre_Gen_var : forall (n : nat) (Gamma : context n) (M C : term n),
  Gamma |- M ; C -> forall x : fin n, M = x -> typeof x Gamma ~= C.
Proof.
 induction 1; try discriminate 1; intros.
(* var *)
  replace x with (bot (n := n)).
     apply conv_ref.
     apply var_inj.
       assumption.
(* weakening *)
  elim liftterm_var with n A x.
     destruct 1.
       rewrite H3.
       simpl.
       apply conv_liftterm.
       auto.
     assumption.
(* conversion *)
  apply conv_trans with B; auto.
Qed.

Theorem Gen_var : forall (n : nat) (Gamma : context n) (x : fin n) (C : term n),
  Gamma |- x ; C -> typeof x Gamma ~= C.
Proof.
  intros.
  apply pre_Gen_var with (var x); auto.
Qed.

Lemma pre_Gen_pi : forall n (Gamma : context n) M C ,
  Gamma |- M ; C -> forall A B, M = pi A B ->
  exists s1, exists s2, exists s3, rule s1 s2 s3 /\
  Gamma |- A ; srt s1 /\ ((Gamma, A) : context (S n)) |- B ; srt s2 /\ C ->> srt s3.
Proof.
 induction 1; try discriminate 1; intros.
(* weakening *)
  elim liftterm_pi with n A A0 B0.
   intro A1.
     destruct 1.
     rename x into B1.
     destruct H2.
     destruct H3.
     elim IHPTS1 with A1 B1.
      intro s1.
        destruct 1.
        rename x into s2.
        destruct H5.
        rename x into s3.
        destruct H5.
        destruct H6.
        destruct H7.
        split with s1.
        split with s2.
        split with s3.
        assert (((Gamma,C) : context (S n)) |- A0 ; srt s1).
          rewrite <- H3.
          apply weakening with (B := srt (n:=n) s1) (s:=s); assumption.
        split.
         assumption.
        split.
         assumption.
        split.
         rewrite <- H4.
           apply Weakening with (n:=S n) (Delta := (Gamma, A1)) (A := srt (n:=S n) s2) (rho := Sfun (up (n := n))).
            assumption.
            split with s1.
              assumption.
            unfold subctxt.
              destruct x; simpl.
               apply liftterm_liftterm'.
               rewrite <- H3.
                 apply liftterm_liftterm'.
         apply red_liftterm with (N := srt (n:=n) s3).
           assumption.
      assumption.
   assumption.
(* product *)
  split with s1.
    split with s2.
    split with s3.
    rewrite <- pi_injl with n A A0 B B0.
     split.
      assumption.
     split.
      assumption.
     split.
      rewrite <- pi_injr with n A A0 B B0; assumption.
      apply red_ref.
     assumption.
(* conversion *)
  elim IHPTS1 with A0 B0.
   intro s1.
     destruct 1.
     rename x into s2.
     destruct H3.
     rename x into s3.
     destruct H3.
     destruct H4.
     destruct H5.
     split with s1.
     split with s2.
     split with s3.
     split.
      assumption.
     split.
      assumption.
     split.
      assumption.
      apply Gen_conv_srt.
        apply conv_trans with B.
         apply conv_sym.
           assumption.
         apply conv_red.
           assumption.
   assumption.
Qed.

Theorem Gen_pi : forall n (Gamma : context n) A B C,
  Gamma |- pi A B ; C -> exists s1, exists s2, exists s3,
  rule s1 s2 s3 /\ Gamma |- A ; srt s1 /\ ((Gamma, A) : context (S n)) |- B ; srt s2 /\ C ->> srt s3.
Proof.
  intros.
  apply pre_Gen_pi with (pi A B); auto.
Qed.

Lemma Gen_pi' : forall n (Gamma : context n) A B s3,
  Gamma |- pi A B ; srt s3 -> exists s1, exists s2,
  rule s1 s2 s3 /\ Gamma |- A ; srt s1 /\ ((Gamma, A) : context (S n)) |- B ; srt s2.
Proof.
  intros.
  elim Gen_pi with n Gamma A B (srt (n:=n) s3).
   intro s1.
     destruct 1.
     rename x into s2.
     destruct H0.
     rename x into s3'.
     destruct H0.
     destruct H1.
     destruct H2.
     split with s1.
     split with s2.
     split.
      rewrite red_srt_inj with n s3 s3'; assumption.
     split; assumption.
   assumption.
Qed.

Lemma pre_Gen_lda : forall n (Gamma : context n) M C,
  Gamma |- M ; C ->
  forall A N, M = lda A N ->
  exists B, exists s,
  Gamma |- pi A B ; srt s /\ ((Gamma, A) : context (S n)) |- N ; B /\ C ~= pi A B.
Proof.
  induction 1; try discriminate 1; intros.
(* weakening *)
   elim liftterm_lda with n A A0 N.
    intro A0'.
      destruct 1.
      rename x into N'.
      destruct H2.
      destruct H3.
      elim IHPTS1 with A0' N'.
       intro B0'.
         destruct 1.
         rename x into t.
         destruct H5.
         destruct H6.
         split with (subvar B0' (Sfun (up (n:=n)))).
         split with t.
         rewrite <- H3.
         rewrite <- H4.
         split.
          apply weakening with (A := pi A0' B0') (B := srt (n := n) t) (s := s); assumption.
         split.
          apply Weakening with (n := S n) (Delta := (Gamma, A0')).
           assumption.
           apply Weak_valid with (n:=n) (Gamma:=Gamma) (s:=s).
            apply Context_Validity with N' B0'.
              assumption.
            assumption.
            unfold subctxt.
              destruct x; simpl; apply liftterm_liftterm'.
           apply conv_liftterm with (n := n) (M := B) (N := pi A0' B0').
             assumption.
        assumption.
    assumption.
(* abstraction *)
   split with B.
     split with s3.
     rewrite <- lda_injl with n A A0 b N.
      split.
       apply product with s1 s2; assumption.
      split.
       rewrite <- lda_injr with n A A0 b  N; assumption.
       apply conv_ref.
      assumption.
(* conversion *)
   elim IHPTS1 with A0 N.
    intro B0.
      destruct 1.
      rename x into t.
      destruct H3.
      destruct H4.
      split with B0.
      split with t.
      split.
       assumption.
      split.
       assumption.
       apply conv_trans with B.
        apply conv_sym.
          assumption.
        assumption.
    assumption.
Qed.

Theorem Gen_lda : forall n (Gamma : context n) A M C,
  Gamma |- lda A M ; C ->
  exists B, exists s,
  Gamma |- pi A B ; srt s /\ ((Gamma, A) : context (S n)) |- M ; B /\ C ~= pi A B.
Proof.
  intros.
  apply pre_Gen_lda with (lda A M); auto.
Save.

Lemma Gen_lda' : forall n (Gamma : context n) A M C,
  Gamma |- lda A M ; C ->
  exists B, exists s1, exists s2, exists s3,
  rule s1 s2 s3 /\ Gamma |- A ; srt s1 /\ ((Gamma, A) : context (S n)) |- B ; srt s2 /\
  ((Gamma, A) : context (S n)) |- M ; B /\ C ~= pi A B.
Proof.
  intros.
  elim Gen_lda with n Gamma A M C.
   intro B.
     destruct 1.
     rename x into s3.
     destruct H0.
     destruct H1.
     split with B.
     elim Gen_pi' with n Gamma A B s3.
      intro s1.
        destruct 1.
        rename x into s2.
        destruct H3.
        destruct H4.
        split with s1.
        split with s2.
        split with s3.
        auto.
      assumption.
   assumption.
Qed.

Lemma pre_Gen_app : forall n (Gamma : context n) M C,
  Gamma |- M ; C ->
  forall N P, M = app N P ->
  exists A, exists B,
  Gamma |- N ; pi A B /\ Gamma |- P ; A /\ C ~= subbot B P.
Proof.
  induction 1; try discriminate 1; intros.
(* weakening *)
   elim liftterm_app with n A N P.
    intro N0.
      destruct 1.
      rename x into P0.
      destruct H2.
      destruct H3.
      rewrite <- H3.
      rewrite <- H4.
      elim IHPTS1 with N0 P0.
      intro A0.
      destruct 1.
      rename x into B0.
      destruct H5.
      destruct H6.
      split with (liftterm A0).
      split with (subvar B0 (Sfun (up (n:=n)))).
      split.
       apply weakening with (B := pi A0 B0) (s := s); assumption.
      split.
       apply weakening with s; assumption.
         rewrite <- liftterm_subbot.
         apply conv_liftterm.
         assumption.
       assumption.
    assumption.
(* application *)
   split with A.
     split with B.
     split.
      rewrite <- app_injl with n F N a P; assumption.
     rewrite <- app_injr with n F N a P; auto.
(* conversion *)
   elim IHPTS1 with N P.
    intro A0.
      destruct 1.
      rename x into B0.
      destruct H3.
      destruct H4.
      split with A0.
      split with B0.
      split.
       assumption.
      split.
       assumption.
       apply conv_trans with B.
        apply conv_sym.
	  assumption.
	assumption.
    assumption.
Qed.

Theorem Gen_app : forall n (Gamma : context n) M N C,
  Gamma |- app M N ; C ->
  exists A, exists B,
  Gamma |- M ; pi A B /\ Gamma |- N ; A /\ C ~= subbot B N.
Proof.
  intros.
  apply pre_Gen_app with (app M N); auto.
Qed.

Theorem Type_Validity : forall n (Gamma : context n) M A,
  Gamma |- M ; A ->
  (exists s, A = srt s) \/
  (exists s, Gamma |- A ;srt s).
Proof.
  induction 1.
(* axioms *)
   left.
     split with t.
     reflexivity.
(* start *)
   right.
     split with s.
     apply weakening with (B := srt (n:=n) s) (s:=s); assumption.
(* weakening *)
   destruct IHPTS1; destruct H1; rename x into t.
    left.
      split with t.
      rewrite H1.
      reflexivity.
    right.
      split with t.
      apply weakening with (B := srt (n:=n) t) (s:=s); assumption.
(* product *)
   left.
     split with s3.
     reflexivity.
(* application *)
   destruct IHPTS1; destruct H1.
    discriminate H1.
    rename x into s3.
      elim Gen_pi' with n Gamma A B s3.
      intro s1.
      destruct 1.
      rename x into s2.
      destruct H2.
      destruct H3.
      right.
      split with s2.
      apply Substitution_bot with (B := srt (n:=S n) s2) (N := a) (A := A); assumption.
    assumption.
(* abstraction *)
   right.
     split with s3.
     apply product with s1 s2; assumption.
(* conversion *)
   right.
     split with s.
     assumption.
Qed.

Theorem Context_Conversion : forall n (Gamma : context n) M A, Gamma |- M ; A ->
  forall Delta, Gamma ~=c Delta -> valid Delta ->
  Delta |- M ; A.
Proof.
  induction 1; simpl.
(* axioms *)
   destruct Delta.
     intros _ _.
     apply axioms.
     assumption.
(* start *)
   destruct Delta.
     rename c into Delta.
     rename t into B.
     destruct 2.     
     rename x into t.
     apply conversion with (liftterm B) s.
      apply conv_sym.
        exact (H0 bot).
      apply start with t.
        assumption.
      apply weakening with (B := srt (n:=n) s) (s := t).
        apply IHPTS.
         apply conv_ctxt_injl with A B.
           assumption.
         apply Context_Validity with B (srt (n:=n) t); assumption.
           assumption.
(* weakening *)
   destruct Delta.
     rename c into Delta.
     rename t into D.
     destruct 2.
     rename x into t.
     apply weakening with t.
      apply IHPTS1.
       apply conv_ctxt_injl with C D.
         assumption.
       apply Context_Validity with D (srt (n:=n) t); assumption.
      assumption.
(* product *)
   intros.
     apply product with s1 s2; auto.
     apply IHPTS2.
      apply conv_ctxt_build; auto.
      split with s1.
        apply IHPTS1; assumption.
(* application *)
   intros.
     apply application with A.
      apply IHPTS1; assumption.
      apply IHPTS2; assumption.
(* abstraction *)
   intros.
     assert (((Gamma, A) : context (S n)) ~=c (Delta, A)).
       apply conv_ctxt_build; auto.
     assert (Delta |- A ; srt s1).
       apply IHPTS2; assumption.
     assert (valid (n:=S n) (Delta, A)).
       split with s1.
       assumption.
     apply abstraction with s1 s2 s3; auto.
(* conversion *)
   intros.
     apply conversion with B s; auto.
Qed.

