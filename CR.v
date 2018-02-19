Require Export Conv.

(* The Church-Rosser Theorem *)

Lemma par_red1_dmnd : forall n : nat, forall M N : term n, M |> N ->
  forall P, M |> P -> exists Q, N |> Q /\ P |> Q.
Proof.
induction 1; intros.
(* x |> x *)
split with (var x).
  split.
   apply par_red1_var.
   replace P with (var x).
    apply par_red1_var.
    symmetry.
      apply Gen_par_red1_var.
      assumption.
(* s |> s *)
split with (srt (n:=n) s).
  split.
   apply par_red1_srt.
   replace P with (srt (n:=n) s).
    apply par_red1_srt.
    symmetry.
      apply Gen_par_red1_srt.
      assumption.
(* app M N |> app M' N' *)
elim Gen_par_red1_app with n M N P; auto.
(* Case P = app M'' N'', with M |> M'' and N |> N'' *)
  destruct 1.
  rename x into M''.
  destruct H2.
  rename x into N''.
  destruct H2.
  destruct H3.
  elim IHpar_red1_1 with M''; auto.
  destruct 1.
  rename x into M0.
  elim IHpar_red1_2 with N''; auto.
  destruct 1.
  rename x into N0.
  split with (app M0 N0).
  split.
   apply par_red1_app; assumption.
   rewrite H4.
     apply par_red1_app; assumption.
(* Case P = subbot R'' N'', where M = lda A R, R |> R'' and N |> N'' *)
  destruct 1.
  rename x into A.
  destruct H2.
  rename x into N''.
  destruct H2.
  rename x into R.
  destruct H2.
  rename x into R''.
  destruct H2.
  destruct H3.
  destruct H4.
  elim IHpar_red1_1 with (lda A R'').
  destruct 1.
  rename x into M0.
  elim Gen_par_red1_lda with n A M0 R''; auto.
  destruct 1.
  rename x into A0.
  rename x0 into R0.
  destruct H8.
  destruct H9.
  elim Gen_par_red1_lda with n A M' R; auto.
  destruct 1.
  rename x into A'.
  rename x0 into R'.
  destruct H11.
  destruct H12.
  elim Gen_par_red1_lda with n A' M0 R'; auto.
  destruct 1.
  destruct H14.
  destruct H15.
  rewrite H10 in H16.
  replace x with A0 in H14.
  replace x0 with R0 in H15.
  clear x x0 H16.
  elim IHpar_red1_2 with N''; auto.
  destruct 1.
  rename x into N0.
  split with (subbot R0 N0).
  split.
   rewrite H13.
     apply par_red1_beta; assumption.
   rewrite H5.
     apply par_red1_subbot; assumption.
  apply lda_injr with A0 x.
    assumption.
  apply lda_injl with R0 x0.
    assumption.
  rewrite <- H13.
    assumption.
  rewrite <- H2.
    assumption.
  rewrite H2.
    apply par_red1_lda; auto.
(* pi A B |> pi A' B' *)
elim Gen_par_red1_pi with n A P B; auto.
  destruct 1.
  rename x into A''.
  rename x0 into B''.
  destruct H2.
  destruct H3.
  elim IHpar_red1_1 with A''; auto.
  destruct 1.
  rename x into A0.
  elim IHpar_red1_2 with B''; auto.
  destruct 1.
  rename x into B0.
  split with (pi A0 B0).
  split.
   apply par_red1_pi; assumption.
   rewrite H4.
     apply par_red1_pi; assumption.
(* lda A M |> lda A' M' *)
elim Gen_par_red1_lda with n A P M; auto.
  destruct 1.
  rename x into A''.
  rename x0 into M''.
  destruct H2.
  destruct H3.
  elim IHpar_red1_1 with A''; auto.
  destruct 1.
  rename x into A0.
  elim IHpar_red1_2 with M''; auto.
  destruct 1.
  rename x into M0.
  split with (lda A0 M0).
  split.
   apply par_red1_lda; assumption.
   rewrite H4.
     apply par_red1_lda; assumption.
(* app (lda A M) N |> subbot M' N' *)
elim Gen_par_red1_app with n (lda A M) N P; auto.
(* Case P = app P'' N'', where lda A M |> P'' and N |> N'' *)
 destruct 1.
   rename x into P''.
   destruct H2.
   rename x into N''.
   destruct H2.
   destruct H3.
   elim Gen_par_red1_lda with n A P'' M; auto.
   destruct 1.
   rename x into A''.
   rename x0 into M''.
   destruct H5.
   destruct H6.
   elim IHpar_red1_1 with M''; auto.
   destruct 1.
   rename x into M0.
   elim IHpar_red1_2 with N''; auto.
   destruct 1.
   rename x into N0.
   split with (subbot M0 N0).
   split.
    apply par_red1_subbot; assumption.
    rewrite H4.
      rewrite H7.
      apply par_red1_beta; assumption.
(* Case P = subbot M'' N'', where M |> M'' and N |> N'' *)
 destruct 1.
   destruct H2.
   rename x0 into N''.
   destruct H2.
   destruct H2.
   rename x1 into M''.
   destruct H2.
   destruct H3.
   destruct H4.
   replace x0 with M in H4.
   clear x x0 H2.
   elim IHpar_red1_1 with M''; auto.
   destruct 1.
   rename x into M0.
   elim IHpar_red1_2 with N''; auto.
   destruct 1.
   rename x into N0.
   split with (subbot M0 N0).
   split.
    apply par_red1_subbot; assumption.
    rewrite H5.
    apply par_red1_subbot; assumption.
   apply lda_injr with A x.
   assumption.
Qed.

Lemma red_par_red1_comm : forall (n : nat) (M N : term n), M ->> N ->
  forall P : term n, M |> P ->
  exists Q : term n, N |> Q /\ P ->> Q.
Proof.
induction 1; intros.
 elim par_red1_dmnd with n M N P; auto.
   destruct 1.
   rename x into Q.
   split with Q.
   split.
    assumption.
    apply red_par_red1.
      assumption.
 elim IHred1 with P0; auto.
   destruct 1.
   rename x into N0.
   elim IHred2 with N0; auto.
   destruct 1.
   rename x into Q.
   split with Q.
   split.
    assumption.
    apply red_trans with N0; assumption.
Qed.

Theorem red_dmnd : forall (n : nat) (M N : term n), M ->> N ->
  forall P, M ->> P ->
  exists Q, N ->> Q /\ P ->> Q.
Proof.
induction 1; intros.
 elim red_par_red1_comm with n M P N; auto.
   destruct 1.
   rename x into Q.
   split with Q.
   split.
    assumption.
    apply red_par_red1.
      assumption.
 elim IHred1 with P0; auto.
   destruct 1.
   rename x into N0.
   elim IHred2 with N0; auto.
   destruct 1.
   rename x into Q.
   split with Q.
   split.
    assumption.
    apply red_trans with N0; assumption.
Qed.

Theorem Church_Rosser : forall (n : nat) (M N : term n),
  M ~= N -> exists P, M ->> P /\ N ->> P.
Proof.
induction 1.
 split with N.
   split.
    apply red_par_red1.
      assumption.
    apply red_ref.
 destruct IHconv.
   rename x into P.
   destruct H0.
   split with P.
   auto.
 destruct IHconv1.
   rename x into Q.
   destruct H1.
   destruct IHconv2.
   rename x into Q'.
   destruct H3.
   elim red_dmnd with n N Q Q'; auto.
   destruct 1.
   rename x into R.
   split with R.
   split.
    apply red_trans with Q; assumption.
    apply red_trans with Q'; assumption.
Qed.

Lemma Gen_conv_var : forall (n : nat) (M : term n) (x : fin n),
  M ~= x -> M ->> x.
Proof.
intros.
elim Church_Rosser with n M (var x); auto.
destruct 1.
rename x0 into N.
replace (var x) with N.
 assumption.
 apply Gen_red_var.
   assumption.
Qed.

Lemma Gen_conv_srt : forall (n : nat) (M : term n) (s : sort),
  M ~= srt s -> M ->> srt s.
Proof.
intros.
elim Church_Rosser with n M (srt (n:=n) s); auto.
destruct 1.
rename x into N.
replace (srt (n:=n) s) with N.
assumption.
apply Gen_red_srt.
assumption.
Qed.

Lemma Gen_conv_pi : forall (n : nat) (A : term n) (B : term (S n)) (P : term n),
  pi A B ~= P -> exists A', exists B', A ->> A' /\ B ->> B' /\ P ->> pi A' B'.
Proof.
intros.
elim Church_Rosser with n (pi A B) P; auto.
destruct 1.
rename x into Q.
elim Gen_red_pi with n A B Q; auto.
destruct 1.
rename x into A'.
rename x0 into B'.
destruct H2.
destruct H3.
split with A'.
split with B'.
split.
 assumption.
split.
 assumption.
 rewrite <- H2.
   assumption.
Qed.

Lemma Gen_conv_lda : forall (n : nat) (A : term n) (B : term (S n)) (P : term n),
  lda A B ~= P -> exists A', exists B', A ->> A' /\ B ->> B' /\ P ->> lda A' B'.
Proof.
intros.
elim Church_Rosser with n (lda A B) P; auto.
destruct 1.
rename x into Q.
elim Gen_red_lda with n A B Q; auto.
destruct 1.
rename x into A'.
rename x0 into B'.
destruct H2.
destruct H3.
split with A'.
split with B'.
split.
 assumption.
split.
 assumption.
 rewrite <- H2.
   assumption.
Qed.

Lemma conv_var_inj : forall (n : nat) (x y : fin n),
  x ~= y -> x = y.
Proof.
intros.
apply red_var_inj.
apply Gen_conv_var.
assumption.
Qed.

Lemma conv_srt_inj : forall (n : nat) (s t : sort),
  srt (n:=n) s ~= srt t -> s = t.
Proof.
intros.
apply red_srt_inj with n.
apply Gen_conv_srt.
assumption.
Qed.

Lemma conv_pi_injl : forall (n : nat) (A A' : term n) (B B' : term (S n)),
  pi A B ~= pi A' B' -> A ~= A'.
Proof.
intros.
elim Gen_conv_pi with n A B (pi A' B'); auto.
destruct 1.
rename x into A0.
rename x0 into B0.
destruct H0.
destruct H1.
apply conv_trans with A0.
 apply conv_red.
   assumption.
 apply conv_sym.
   apply conv_red.
   apply red_pi_injl with B' B0.
   assumption.
Qed.

Lemma conv_pi_injr : forall (n : nat) (A A' : term n) (B B' : term (S n)),
  pi A B ~= pi A' B' -> B ~= B'.
Proof.
intros.
elim Gen_conv_pi with n A B (pi A' B'); auto.
destruct 1.
rename x into A0.
rename x0 into B0.
destruct H0.
destruct H1.
apply conv_trans with B0.
 apply conv_red.
   assumption.
 apply conv_sym.
   apply conv_red.
   apply red_pi_injr with A' A0.
   assumption.
Qed.

Lemma conv_lda_injl : forall (n : nat) (A A' : term n) (B B' : term (S n)),
  lda A B ~= lda A' B' -> A ~= A'.
Proof.
intros.
elim Gen_conv_lda with n A B (lda A' B'); auto.
destruct 1.
rename x into A0.
rename x0 into B0.
destruct H0.
destruct H1.
apply conv_trans with A0.
 apply conv_red.
   assumption.
 apply conv_sym.
   apply conv_red.
   apply red_lda_injl with B' B0.
   assumption.
Qed.

Lemma conv_lda_injr : forall (n : nat) (A A' : term n) (B B' : term (S n)),
  lda A B ~= lda A' B' -> B ~= B'.
Proof.
intros.
elim Gen_conv_lda with n A B (lda A' B'); auto.
destruct 1.
rename x into A0.
rename x0 into B0.
destruct H0.
destruct H1.
apply conv_trans with B0.
 apply conv_red.
   assumption.
 apply conv_sym.
   apply conv_red.
   apply red_lda_injr with A' A0.
   assumption.
Qed.

Lemma conv_subvar_inj : forall (m n : nat) (M N : term m) (rho : fin m -> fin n),
  injective rho -> subvar M rho ~= subvar N rho -> M ~= N.
Proof.
intros.
elim Church_Rosser with n (subvar M rho) (subvar N rho); auto.
destruct 1.
rename x into P.
elim red_subvar_inv with m n M rho P; auto.
destruct 1.
rename x into M0.
rewrite H4 in H2.
apply conv_trans with M0.
 apply conv_red.
   assumption.
 apply conv_sym.
   apply conv_red.
   apply red_subvar_inj with n rho; assumption.
Qed.    

Lemma conv_liftterm_inj : forall n (M N : term n), liftterm M ~= liftterm N -> M ~= N.
unfold liftterm.
intros n M N.
apply conv_subvar_inj.
exact (up_inj n).
Qed.

Lemma not_conv_pi_srt : forall (n : nat) (A : term n) (B : term (S n)) (s : sort),
  ~(pi A B ~= srt s).
Proof.
intros.
intro.
elim not_red_pi_srt with n A B s.
apply Gen_conv_srt.
assumption.
Qed.
