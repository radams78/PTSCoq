Require Export Subst.

(* Parallel One-Step Reduction *)

Inductive par_red1 : forall n, term n -> term n -> Prop :=
  par_red1_var : forall n (x : fin n), par_red1 _ x x |
  par_red1_srt : forall n s, par_red1 n (srt s) (srt s) |
  par_red1_app : forall n (M M' N N' : term n),
    par_red1 _ M M' -> par_red1 _ N N' -> par_red1 _ (app M N) (app M' N') |
  par_red1_pi : forall n (A A' : term n) (B B' : term (S n)),
    par_red1 _ A A' -> par_red1 _ B B' -> par_red1 _ (pi A B) (pi A' B') |
  par_red1_lda : forall n (A A' : term n) (M M' : term (S n)),
    par_red1 _ A A' -> par_red1 _ M M' -> par_red1 _ (lda A M) (lda A' M') |
  par_red1_beta : forall n (M M' : term (S n)) (A N N' : term n),
    par_red1 _ M M' -> par_red1 _ N N' -> par_red1 _ (app (lda A M) N) (subbot M' N').
Implicit Arguments par_red1 [n].
Notation "M |> N" := (par_red1 M N) (at level 80).

Lemma par_red1_ref : forall n : nat, forall M : term n, M |> M.
Proof.
induction M.
 apply par_red1_var.
 apply par_red1_srt.
 apply par_red1_app; assumption.
 apply par_red1_pi; assumption.
 apply par_red1_lda; assumption.
Qed.
Hint Resolve par_red1_ref.

(* Generation lemmas for parallel one-step reduction *)

Lemma pre_Gen_par_red1_var : forall n (M N : term n),
  M |> N -> forall x : fin n, M = x -> N = x.
Proof.
induction 1; try discriminate 1.
auto.
Qed.

Lemma Gen_par_red1_var : forall n (x : fin n) (N : term n),
  x |> N -> N = x.
Proof.
intros.
apply pre_Gen_par_red1_var with (var x); auto.
Qed.

Lemma pre_Gen_par_red1_srt : forall n (M N : term n), M |> N -> forall s, M = srt s -> N = srt s.
Proof.
induction 1; try discriminate 1.
auto.
Qed.

Lemma Gen_par_red1_srt : forall n s (N : term n), srt s |> N -> N = srt s.
Proof.
intros.
apply pre_Gen_par_red1_srt with (srt (n := n) s); auto.
Qed.

Lemma pre_Gen_par_red1_app : forall n (M N : term n), M |> N ->
  forall P Q, M = app P Q ->
  (exists P', exists Q', P |> P' /\ Q |> Q' /\ N = app P' Q') \/
  (exists A, exists Q', exists R, exists R', P = lda A R /\ Q |> Q' /\ R |> R' /\ N = subbot R' Q').
Proof.
induction 1; try discriminate 1.
(* The case: app M N |> app M' N' *)
 left.
   replace P with M.
    replace Q with N.
     clear P Q H1.
     split with M'.
     split with N'.
     auto.
    eapply app_injr.
    apply H1.
   eapply app_injl.
   apply H1.
(* The case: app (lda A M) N |> subbot M' N' *)
 right.
   replace P with (lda A M).
    replace Q with N.
     clear P Q H1.
     split with A.
     split with N'.
     split with M.
     split with M'.
     auto.
    eapply app_injr.
    apply H1.
   eapply app_injl.
   apply H1.
Qed.

Lemma Gen_par_red1_app : forall n (P Q N : term n), app P Q |> N ->
  (exists P', exists Q', P |> P' /\ Q |> Q' /\ N = app P' Q') \/
  (exists A, exists Q', exists R, exists R', P = lda A R /\ Q |> Q' /\ R |> R' /\ N = subbot R' Q').
Proof.
intros.
apply pre_Gen_par_red1_app with (app P Q); auto.
Qed.

Lemma pre_Gen_par_red1_pi : forall n (M N : term n), M |> N ->
  forall A B, M = pi A B ->
  exists A', exists B', A |> A' /\ B |> B' /\ N = pi A' B'.
Proof.
induction 1; try discriminate 1.
intros.
replace A0 with A.
 replace B0 with B.
  clear A0 B0 H1.
  split with A'.
  split with B'.
  auto.
 eapply pi_injr.
 apply H1.
eapply pi_injl.
apply H1.
Qed.

Lemma Gen_par_red1_pi : forall n (A N : term n) (B : term (S n)), pi A B |> N ->
  exists A', exists B', A |> A' /\ B |> B' /\ N = pi A' B'.
Proof.
intros.
apply pre_Gen_par_red1_pi with (pi A B); auto.
Qed.

Lemma pre_Gen_par_red1_lda : forall n (M N : term n), M |> N ->
  forall A P, M = lda A P ->
  exists A', exists P', A |> A' /\ P |> P' /\ N = lda A' P'.
Proof.
induction 1; try discriminate 1.
intros.
replace A0 with A.
 replace P with M.
  clear A0 P H1.
  split with A'.
  split with M'.
  auto.
 eapply lda_injr.
 apply H1.
eapply lda_injl.
apply H1.
Qed.

Lemma Gen_par_red1_lda : forall n (A N : term n) (P : term (S n)), lda A P |> N ->
  exists A', exists P', A |> A' /\ P |> P' /\ N = lda A' P'.
Proof.
intros.
apply pre_Gen_par_red1_lda with (lda A P); auto.
Qed.

(* Injectivity lemmas for parallel one-step reduction *)

Lemma par_red1_var_inj : forall n (x y : fin n), x |> y -> x = y.
Proof.
intros.  
symmetry.
apply var_inj.
apply Gen_par_red1_var.
auto.
Qed.

Lemma par_red1_srt_inj : forall n s t, srt (n:=n) s |> srt t -> s = t.
Proof.
intros.
symmetry.
apply srt_inj with n.
apply Gen_par_red1_srt.
assumption.
Qed.

Lemma par_red1_pi_injl : forall n (A A' : term n) (B B' : term (S n)),
  pi A B |> pi A' B' -> A |> A'.
Proof.
intros.
elim Gen_par_red1_pi with n A (pi A' B') B.
 destruct 1.
   rename x into A''.
   rename x0 into B''.
   destruct H0.
   destruct H1.
   replace A' with A''.
  auto.
  symmetry.
    eapply pi_injl.
    apply H2.
 auto.
Qed.

Lemma par_red1_pi_injr : forall (n : nat) (A A' : term n) (B B' : term (S n)),
  pi A B |> pi A' B' -> B |> B'.
Proof.
intros.
elim Gen_par_red1_pi with n A (pi A' B') B.
 destruct 1.
   rename x into A''.
   rename x0 into B''.
   destruct H0.
   destruct H1.
   replace B' with B''.
  auto.
  symmetry.
    eapply pi_injr.
    apply H2.
 auto.
Qed.

Lemma par_red1_lda_injl : forall n (A A' : term n) (M M' : term (S n)),
  lda A M |> lda A' M' -> A |> A'.
Proof.
intros.
elim Gen_par_red1_lda with n A (lda A' M') M.
 destruct 1.
   rename x into A''.
   rename x0 into M''.
   destruct H0.
   destruct H1.
   replace A' with A''.
  auto.
  symmetry.
    eapply lda_injl.
    apply H2.
 auto.
Qed.

Lemma par_red1_lda_injr : forall (n : nat) (A A' : term n) (M M' : term (S n)),
  lda A M |> lda A' M' -> M |> M'.
Proof.
intros.
elim Gen_par_red1_lda with n A (lda A' M') M.
 destruct 1.
   rename x into A''.
   rename x0 into M''.
   destruct H0.
   destruct H1.
   replace M' with M''.
  auto.
  symmetry.
    eapply lda_injr.
    apply H2.
 auto.
Qed.

(* Interaction between parallel one-step reduction and substitution *)

Lemma par_red1_subvar : forall n (M N : term n), M |> N ->
  forall m (rho : fin n -> fin m), subvar M rho |> subvar N rho.
Proof.
induction 1; simpl; intros.
 apply par_red1_var.
 apply par_red1_srt.
 apply par_red1_app.
  apply IHpar_red1_1.
  apply IHpar_red1_2.
 apply par_red1_pi.
  apply IHpar_red1_1.
  apply IHpar_red1_2.
 apply par_red1_lda.
  apply IHpar_red1_1.
  apply IHpar_red1_2.
 rewrite subvar_subbot.
   apply par_red1_beta.
  apply IHpar_red1_1.
  apply IHpar_red1_2.
Qed.

Lemma pre_par_red1_subvar_inv : forall n (M N : term n), M |> N ->
  forall m (P : term m) (rho : fin m -> fin n),
  M = subvar P rho -> exists Q, N = subvar Q rho /\ P |> Q.
Proof.
induction 1.
(* x |> x *)
intros.
split with P.
auto.   
(* s |> s *)
intros.
split with P.
auto.
(* M N |> M' N' *)
 intros.
   elim subvar_app with m P n rho M N; auto.
   destruct 1.
   rename x into M0.
   rename x0 into N0.
   destruct H2.
   destruct H3.
   elim IHpar_red1_1 with m M0 rho; auto.
   destruct 1.
   rename x into M1.
   elim IHpar_red1_2 with m N0 rho; auto.
   destruct 1.
   rename x into N1.
   split with (app M1 N1).
   split.
  simpl.
    apply app_wd; auto.
  rewrite H2.
    apply par_red1_app; auto.
(* pi A B |> pi A' B' *)
 intros.
   elim subvar_pi with m P n rho A B; auto.
   destruct 1.
   rename x into A0.
   rename x0 into B0.
   destruct H2.
   destruct H3.
   elim IHpar_red1_1 with m A0 rho; auto.
   destruct 1.
   rename x into A1.
   elim IHpar_red1_2 with (S m) B0 (Sfun rho); auto.
   destruct 1.
   rename x into B1.
   split with (pi A1 B1).
   split.
  simpl.
    apply pi_wd; auto.
  rewrite H2.
    apply par_red1_pi; auto.
(* lda A M |> lda A' M' *)
 intros.
   elim subvar_lda with m P n rho A M; auto.
   destruct 1.
   rename x into A0.
   rename x0 into M0.
   destruct H2.
   destruct H3.
   elim IHpar_red1_1 with m A0 rho; auto.
   destruct 1.
   rename x into A1.
   elim IHpar_red1_2 with (S m) M0 (Sfun rho); auto.
   destruct 1.
   rename x into M1.
   split with (lda A1 M1).
   split.
  simpl.
    apply lda_wd; auto.
  rewrite H2.
    apply par_red1_lda; auto.
(* app (lda A M) N |> subbot M' N' *)
 intros.
   elim subvar_app with m P n rho (lda A M) N; auto.
   destruct 1.
   rename x into P0.
   rename x0 into N0.
   destruct H2.
   destruct H3.
   elim subvar_lda with m P0 n rho A M; auto.
   destruct 1.
   rename x into A0.
   rename x0 into M0.
   destruct H5.
   destruct H6.
   rewrite H5 in H2.
   clear P0 H3 H5.
   elim IHpar_red1_1 with (S m) M0 (Sfun rho); auto.
   destruct 1.
   rename x into M1.
   elim IHpar_red1_2 with m N0 rho; auto.
   destruct 1.
   rename x into N1.
   split with (subbot M1 N1).
   split.
  rewrite H3.
    rewrite H8.
    symmetry.
    apply subvar_subbot.
  rewrite H2.
    apply par_red1_beta; auto.
Qed.

Lemma par_red1_subvar_inv : forall m n (P : term m) (rho : fin m -> fin n) (N : term n),
  subvar P rho |> N ->
  exists Q, N = subvar Q rho /\ P |> Q.
Proof.
intros.
apply pre_par_red1_subvar_inv with (subvar P rho); auto.
Qed.

Lemma par_red1_subvar_inj : forall (m n : nat) (M N : term m) (rho : fin m -> fin n),
  injective rho -> subvar M rho |> subvar N rho -> M |> N.
Proof.
intros.
elim par_red1_subvar_inv with m n M rho (subvar N rho); auto.
destruct 1.
rename x into N'.
replace N with N'.
auto.
apply subvar_inj with n rho; auto.
Qed.

Lemma par_red1_liftterm : forall (n : nat) (M N : term n), M |> N -> liftterm M |> liftterm N.
Proof.
intros.
unfold liftterm.
apply par_red1_subvar.
assumption.
Qed.

Lemma par_red1_liftterm_inv : forall (n : nat) (P : term n) (N : term (S n)),
  liftterm P |> N ->
  exists Q : term n, N = liftterm Q /\ P |> Q.
Proof.
intros.
unfold liftterm.
apply par_red1_subvar_inv.
assumption.
Qed.

Lemma par_red1_liftterm_inj : forall (n : nat) (M N : term n), liftterm M |> liftterm N -> M |> N.
Proof.
unfold liftterm.
intros n M N.
apply par_red1_subvar_inj.
exact (up_inj n).
Qed.

Definition par_red1_sub (m n : nat) (rho sigma : fin m -> term n) :=
  forall x, rho x |> sigma x.
Implicit Arguments par_red1_sub [m n].
Notation "rho |s> sigma" := (par_red1_sub rho sigma) (at level 80).

Lemma par_red1_sub_ref : forall (m n : nat) (rho : fin m -> term n), rho |s> rho.
Proof.
unfold par_red1_sub.
auto.
Qed.
Hint Resolve par_red1_sub_ref.

Lemma par_red1_liftsub : forall (m n : nat) (rho sigma : fin m -> term n),
  rho |s> sigma -> liftsub rho |s> liftsub sigma.
Proof.
unfold par_red1_sub.
destruct x; simpl; auto.
apply par_red1_liftterm.
auto.
Qed.

Lemma par_red1_botsub : forall (n : nat) (M N : term n), M |> N -> botsub M |s> botsub N.
Proof.
unfold par_red1_sub.
destruct x; auto.
Qed.

Lemma par_red1_subst : forall (n : nat) (M N : term n), M |> N ->
  forall (m : nat) (rho sigma : fin n -> term m), rho |s> sigma ->
  subst M rho |> subst N sigma.
Proof.
induction 1; simpl; intros.
(* x |> x *)
auto.
(* s |> s *)
apply par_red1_srt.
(* MN |> M'N' *)
apply par_red1_app; auto.
(* pi A B |> pi A' B' *)
apply par_red1_pi; auto.
apply IHpar_red1_2.
apply par_red1_liftsub.
auto.
(* lda A M |> lda A' M' *)
apply par_red1_lda; auto.
apply IHpar_red1_2.
apply par_red1_liftsub.
auto.
(* app (lda A M) N) |> subbot M' N' *)
rewrite subst_subbot.
apply par_red1_beta; auto.
apply IHpar_red1_1.
apply par_red1_liftsub.
auto.
Qed.

Lemma par_red1_subbot : forall n : nat, forall M M' : term (S n), forall N N' : term n,
  M |> M' -> N |> N' -> subbot M N |> subbot M' N'.
Proof.
intros.
unfold subbot.
apply par_red1_subst.
 assumption.
 apply par_red1_botsub.
   assumption.
Qed.

(* Reduction *)

Inductive red (n : nat) : term n -> term n -> Prop :=
  red_par_red1 : forall M N : term n, par_red1 M N -> red _ M N |
  red_trans : forall M N P : term n, red _ M N -> red _ N P -> red _ M P.
Implicit Arguments red [n].
Notation "M ->> N" := (red M N) (at level 80).

Lemma red_ref : forall (n : nat) (M : term n), M ->> M.
Proof.
intros.
apply red_par_red1.
auto.
Qed.
Hint Resolve red_ref.

Lemma red_appl : forall (n : nat) (M M' N : term n), M ->> M' ->
  app M N ->> app M' N.
Proof.
induction 1.
 apply red_par_red1.
   apply par_red1_app; auto.
 apply red_trans with (app N0 N); auto.
Qed.

Lemma red_appr : forall (n : nat) (M N N' : term n), N ->> N' -> app M N ->> app M N'.
Proof.
induction 1.
 apply red_par_red1.
   apply par_red1_app; auto.
 apply red_trans with (app M N); auto.
Qed.

Lemma red_app : forall (n : nat) (M M' N N' : term n), M ->> M' -> N ->> N' -> app M N ->> app M' N'.
Proof.
intros.
apply red_trans with (app M N').
 apply red_appr; auto.
 apply red_appl; auto.
Qed.

Lemma red_pil : forall (n : nat) (A A' : term n) (B : term (S n)), A ->> A' -> pi A B ->> pi A' B.
Proof.
induction 1.
apply red_par_red1.
  apply par_red1_pi; auto.
apply red_trans with (pi N B); auto.
Qed.

Lemma red_pir : forall (n : nat) (A : term n) (B B' : term (S n)), B ->> B' -> pi A B ->> pi A B'.
Proof.
induction 1.
apply red_par_red1.
  apply par_red1_pi; auto.
apply red_trans with (pi A N); auto.
Qed.

Lemma red_pi : forall (n : nat) (A A' : term n) (B B' : term (S n)), A ->> A' -> B ->> B' -> pi A B ->> pi A' B'.
Proof.
intros.
apply red_trans with (pi A B').
 apply red_pir.
   assumption.
 apply red_pil.
   assumption.
Qed.

Lemma red_ldal : forall (n : nat) (A A' : term n) (M : term (S n)), A ->> A' -> lda A M ->> lda A' M.
Proof.
induction 1.
apply red_par_red1.
  apply par_red1_lda; auto.
apply red_trans with (lda N M); assumption.
Qed.

Lemma red_ldar : forall (n : nat) (A : term n) (M M' : term (S n)), M ->> M' -> lda A M ->> lda A M'. 
Proof.
induction 1.
apply red_par_red1.
    apply par_red1_lda; auto.
apply red_trans with (lda A N); assumption.
Qed.

Lemma red_lda : forall (n : nat) (A A' : term n) (M M' : term (S n)), A ->> A' -> M ->> M' -> lda A M ->> lda A' M'.
Proof.
intros.
apply red_trans with (lda A M').
apply red_ldar.
  assumption.
apply red_ldal.
  assumption.
Qed.

Lemma red_beta : forall (n : nat) (A : term n) (M : term (S n)) (N : term n),
  app (lda A M) N ->> subbot M N.
Proof.
intros.
apply red_par_red1.
apply par_red1_beta; apply par_red1_ref.
Qed.

Lemma red_subvar : forall (n : nat) (M N : term n), M ->> N ->
  forall (m : nat) (rho : fin n -> fin m), subvar M rho ->> subvar N rho.
Proof.
induction 1; intros.
apply red_par_red1. 
  apply par_red1_subvar.
  assumption.
apply red_trans with (subvar N rho).
  apply IHred1.
  apply IHred2.
Qed.

Lemma red_liftterm : forall (n : nat) (M N : term n), M ->> N -> liftterm M ->> liftterm N.
Proof.
intros.
unfold liftterm.
apply red_subvar.
assumption.
Qed.

Definition red_sub (m n : nat) (rho sigma : fin m -> term n) := forall x, rho x ->> sigma x.
Implicit Arguments red_sub [m n].
Notation "rho ->>s sigma" := (red_sub rho sigma) (at level 80).

Lemma red_sub_ref : forall m n (rho : fin m -> term n), rho ->>s rho.
Proof.
unfold red_sub.
auto.
Qed.
Hint Resolve red_sub_ref.

Lemma red_liftsub : forall (m n : nat) (rho sigma : fin m -> term n),
  rho ->>s sigma -> liftsub rho ->>s liftsub sigma.
Proof.
unfold red_sub.
destruct x; simpl.
apply red_liftterm.
  auto.
apply red_ref.
Qed.

Lemma red_botsub : forall (n : nat) (M N : term n), M ->> N -> botsub M ->>s botsub N.
Proof.
unfold red_sub.
destruct x; auto.
Qed.

Lemma red_substl : forall (n : nat) (M N : term n), M ->> N ->
  forall (m : nat) (rho : fin n -> term m),
  subst M rho ->> subst N rho.
Proof.
induction 1; intros.
apply red_par_red1.
  apply par_red1_subst; auto.
apply red_trans with (subst N rho).
  apply IHred1.
  apply IHred2.
Qed.

Lemma red_substr : forall (n : nat) (M : term n) (m : nat) (rho sigma : fin n -> term m),
  rho ->>s sigma -> subst M rho ->> subst M sigma.
Proof.
induction M; simpl; auto; intros.
(* Application *)
apply red_app; auto.
(* Product *)
apply red_pi.
 auto.
 apply IHM2.
   apply red_liftsub.
   assumption.
(* Abstraction *)
apply red_lda.
 auto.
 apply IHM2.
   apply red_liftsub.
   assumption.
Qed.

Lemma red_subst : forall (m n : nat) (M N : term n) (rho sigma : fin n -> term m),
  M ->> N -> rho ->>s sigma ->
  subst M rho ->> subst N sigma.
Proof.
intros.
apply red_trans with (subst M sigma).
 apply red_substr.
   assumption.
 apply red_substl.
   assumption.
Qed.
     
Lemma red_subbotl : forall n (M N : term (S n)) P,
  M ->> N -> subbot M P ->> subbot N P.
Proof.
intros.
unfold subbot.
apply red_substl.
assumption.
Qed.

Lemma red_subbotr : forall n (M : term (S n)) P Q,
  P ->> Q -> subbot M P ->> subbot M Q.
Proof.
intros.
unfold subbot.
apply red_substr.
apply red_botsub.
assumption.
Qed.

Lemma red_subbot : forall (n : nat) (M N : term (S n)) (P Q : term n),
  red M N -> red P Q -> red (subbot M P) (subbot N Q).
Proof.
intros.
unfold subbot.
apply red_subst.
 assumption.
 apply red_botsub.
   assumption.
Qed.

Lemma pre_Gen_red_var : forall n (M N : term n), M ->> N -> forall (x : fin n), M = x -> N = x.
Proof.
induction 1.
apply pre_Gen_par_red1_var.
  assumption.
auto.
Qed.

Lemma Gen_red_var : forall n (x : fin n) (N : term n), x ->> N -> N = x.
Proof.
intros.
apply pre_Gen_red_var with (var x); auto.
Qed.

Lemma pre_Gen_red_srt : forall (n : nat) (M N : term n), M ->> N -> forall s, M = srt s -> N = srt s.
Proof.
induction 1.
apply pre_Gen_par_red1_srt.
  assumption. 
auto. 
Qed.

Lemma Gen_red_srt : forall (n : nat) (s : sort) (N : term n), srt s ->> N -> N = srt s.
Proof.
intros. 
apply pre_Gen_red_srt with (srt (n := n) s); auto.
Qed.

Lemma pre_Gen_red_pi : forall (n : nat) (M N : term n), M ->> N ->
  forall A B, M = pi A B ->
  exists A', exists B', N = pi A' B' /\ A ->> A' /\ B ->> B'.
Proof.
induction 1; intros.
(* M |> N *)
 elim pre_Gen_par_red1_pi with n M N A B; auto.
   destruct 1.
   rename x into A'.
   rename x0 into B'.
   destruct H1.
   destruct H2.
   split with A'.
   split with B'.
   split.
    assumption.
   split.
    apply red_par_red1.
      assumption.
    apply red_par_red1.
      assumption.
(* M ->> N ->> P *)
 elim IHred1 with A B; auto.
   destruct 1.
   rename x into A'.
   rename x0 into B'.
   destruct H2.
   destruct H3.
   elim IHred2 with A' B'; auto.
   destruct 1.
   rename x into A''.
   rename x0 into B''.
   destruct H5.
   destruct H6.
   split with A''.
   split with B''.
   split.
    assumption.
   split.
    apply red_trans with A'; assumption.
    apply red_trans with B'; assumption.
Qed.

Lemma Gen_red_pi : forall (n : nat) (A : term n) (B : term (S n)) (N : term n),
  pi A B ->> N ->
  exists A', exists B',
  N = pi A' B' /\ red A A' /\ red B B'.
Proof.
intros.
apply pre_Gen_red_pi with (pi A B); auto.
Qed.

Lemma pre_Gen_red_lda : forall (n : nat) (M N : term n), M ->> N ->
  forall A B, M = lda A B ->
  exists A', exists B', N = lda A' B' /\ A ->> A' /\ B ->> B'.
Proof.
induction 1; intros.
(* M |> N *)
 elim pre_Gen_par_red1_lda with n M N A B; auto.
   destruct 1.
   rename x into A'.
   rename x0 into B'.
   destruct H1.
   destruct H2.
   split with A'.
   split with B'.
   split.
    assumption.
   split.
    apply red_par_red1.
      assumption.
    apply red_par_red1.
      assumption.
(* M ->> N ->> P *)
 elim IHred1 with A B; auto.
   destruct 1.
   rename x into A'.
   rename x0 into B'.
   destruct H2.
   destruct H3.
   elim IHred2 with A' B'; auto.
   destruct 1.
   rename x into A''.
   rename x0 into B''.
   destruct H5.
   destruct H6.
   split with A''.
   split with B''.
   split.
    assumption.
   split.
    apply red_trans with A'; assumption.
    apply red_trans with B'; assumption.
Qed.

Lemma Gen_red_lda : forall (n : nat) (A : term n) (B : term (S n)) (N : term n),
  lda A B ->> N ->
  exists A', exists B',
  N = lda A' B' /\ red A A' /\ red B B'.
Proof.
intros.
apply pre_Gen_red_lda with (lda A B); auto.
Qed.

Lemma red_var_inj : forall n (x y : fin n), x ->> y -> x = y.
Proof.
intros.
apply var_inj.
symmetry.
apply Gen_red_var.
assumption.
Qed.

Lemma red_srt_inj : forall n s t, srt (n:=n) s ->> srt t -> s = t.
Proof.
intros.
apply srt_inj with n.
symmetry.
apply Gen_red_srt.
assumption.
Qed.

Lemma red_pi_injl : forall (n : nat) (A A' : term n) (B B' : term (S n)),
  pi A B ->> pi A' B' -> A ->> A'.
Proof.
intros.
elim Gen_red_pi with n A B (pi A' B'); auto.
destruct 1.
destruct H0.
destruct H1.
replace A' with x.
assumption.
apply pi_injl with x0 B'.
auto.
Qed.

Lemma red_pi_injr : forall (n : nat) (A A' : term n) (B B' : term (S n)),
  pi A B ->> pi A' B' -> B ->> B'.
Proof.
intros.
elim Gen_red_pi with n A B (pi A' B'); auto.
destruct 1.
destruct H0.
destruct H1.
replace B' with x0.
assumption.
apply pi_injr with x A'.
auto.
Qed.

Lemma red_lda_injl : forall (n : nat) (A A' : term n) (B B' : term (S n)),
  lda A B ->> lda A' B' -> A ->> A'.
Proof.
intros.
elim Gen_red_lda with n A B (lda A' B'); auto.
destruct 1.
destruct H0.
destruct H1.
replace A' with x.
assumption.
apply lda_injl with x0 B'.
auto.
Qed.

Lemma red_lda_injr : forall (n : nat) (A A' : term n) (B B' : term (S n)),
  lda A B ->> lda A' B' -> B ->> B'.
Proof.
intros.
elim Gen_red_lda with n A B (lda A' B'); auto.
destruct 1.
destruct H0.
destruct H1.
replace B' with x0.
assumption.
apply lda_injr with x A'.
auto.
Qed.

Lemma not_red_pi_srt : forall (n : nat) (A : term n) (B : term (S n)) (s : sort),
  ~ (pi A B ->> srt s).
Proof.
intros.
intro H.
elim Gen_red_pi with n A B (srt (n := n) s); auto.
destruct 1.
destruct H0.
discriminate H0.
Qed.

Lemma not_red_srt_pi : forall (n : nat) (s : sort) (A : term n) (B : term (S n)),
  not (srt s ->> pi A B).
Proof.
intros.
intro H.
assert (pi A B = srt s).
 apply Gen_red_srt.
   assumption.
 discriminate H0.
Qed.

Lemma pre_red_subvar_inv : forall (n : nat) (M N : term n), M ->> N ->
  forall (m : nat) (M' : term m) (rho : fin m -> fin n), M = subvar M' rho ->
  exists N' : term m, M' ->> N' /\ N = subvar N' rho.
Proof.
induction 1; intros.
(* M |> N *)
 elim par_red1_subvar_inv with m n M' rho N.
  destruct 1. 
    rename x into N'.
    split with N'.
    split.
     apply red_par_red1.
       assumption.
     assumption.
  rewrite <- H0.
    assumption.
(* M ->> N ->> P *)
 elim IHred1 with m M' rho; auto.
 destruct 1.
 rename x into N'.
 elim IHred2 with m N' rho; auto.
 destruct 1.
 rename x into P'.
 split with P'.
 split.
  apply red_trans with N'; assumption.
  assumption.
Qed.

Lemma red_subvar_inv : forall (m n : nat) (M : term m) (rho : fin m -> fin n) (N : term n),
  subvar M rho ->> N -> exists N', M ->> N' /\ N = subvar N' rho.
Proof.
intros.
apply pre_red_subvar_inv with (subvar M rho); auto.
Qed.

Lemma red_liftterm_inv : forall (n : nat) (M : term n) (N : term (S n)),
  liftterm M ->> N -> exists N', M ->> N' /\ N = liftterm N'.
Proof.
unfold liftterm.
intros n M.
apply red_subvar_inv.
Qed.

Lemma red_subvar_inj : forall (m n : nat) (M N : term m) (rho : fin m -> fin n),
  injective rho -> subvar M rho ->> subvar N rho -> M ->> N.
Proof.
intros.
elim red_subvar_inv with m n M rho (subvar N rho); auto.
destruct 1.
replace N with x.
assumption.
apply subvar_inj with n rho; auto.
Qed.

(* Conversion *)

Inductive conv (n : nat) : term n -> term n -> Prop :=
  conv_par_red1 : forall M N : term n, par_red1 M N -> conv _ M N |
  conv_sym : forall M N : term n, conv _ M N -> conv _ N M |
  conv_trans : forall M N P : term n, conv _ M N -> conv _ N P -> conv _ M P.
Implicit Arguments conv [n].
Notation "M ~= N" := (conv M N) (at level 80).

Lemma conv_red : forall (n : nat) (M N : term n), M ->> N -> M ~= N.
Proof.
induction 1.
apply conv_par_red1.
  assumption.
apply conv_trans with N; assumption.
Qed.

Lemma conv_red' : forall n (M N : term n), M ->> N -> N ~= M.
Proof.
intros.
apply conv_sym.
apply conv_red.
assumption.
Qed.

Lemma conv_ref : forall (n : nat) (M : term n), M ~= M.
Proof.
intros.
apply conv_par_red1.
apply par_red1_ref.
Qed.
Hint Resolve conv_ref.

Lemma conv_appl : forall (n : nat) (M M' N : term n), M ~= M' -> app M N ~= app M' N.
Proof.
induction 1.
 apply conv_par_red1.
   apply par_red1_app; auto.
 apply conv_sym.
   assumption.
 apply conv_trans with (app N0 N); assumption.
Qed.

Lemma conv_appr : forall (n : nat) (M N N' : term n), N ~= N' -> app M N ~= app M N'.
Proof.
induction 1.
 apply conv_par_red1.
   apply par_red1_app; auto.
 apply conv_sym.
   assumption.
 apply conv_trans with (app M N); assumption.
Qed.

Lemma conv_app : forall (n : nat) (M M' N N' : term n), M ~= M' -> N ~= N' -> app M N ~= app M' N'.
Proof.
intros.
apply conv_trans with (app M' N).
 apply conv_appl.
   assumption.
 apply conv_appr.
   assumption.
Qed.

Lemma conv_pil : forall (n : nat) (A A' : term n) (B : term (S n)),
  A ~= A' -> pi A B ~= pi A' B.
Proof.
induction 1.
apply conv_par_red1.
  apply par_red1_pi; auto.
apply conv_sym.
  assumption.
apply conv_trans with (pi N B); assumption.
Qed.

Lemma conv_pir : forall (n : nat) (A : term n) (B B' : term (S n)),
  B ~= B' -> pi A B ~= pi A B'.
Proof.
induction 1.
apply conv_par_red1.
  apply par_red1_pi; auto.
apply conv_sym.
  assumption.
apply conv_trans with (pi A N); assumption.
Qed.

Lemma conv_pi : forall (n : nat) (A A' : term n) (B B' : term (S n)),
  A ~= A' -> B ~= B' -> pi A B ~= pi A' B'.
Proof.
intros.
apply conv_trans with (pi A B').
apply conv_pir.
  assumption.
apply conv_pil.
  assumption.
Qed.

Lemma conv_ldal : forall (n : nat) (A A' : term n) (B : term (S n)),
  A ~= A' -> lda A B ~= lda A' B.
Proof.
induction 1.
apply conv_par_red1.
  apply par_red1_lda; auto.
apply conv_sym.
  assumption.
apply conv_trans with (lda N B); assumption.
Qed.

Lemma conv_ldar : forall (n : nat) (A : term n) (B B' : term (S n)),
  B ~= B' -> lda A B ~= lda A B'.
Proof.
induction 1.
apply conv_par_red1.
  apply par_red1_lda; auto.
apply conv_sym.
  assumption.
apply conv_trans with (lda A N); assumption.
Qed.

Lemma conv_lda : forall (n : nat) (A A' : term n) (B B' : term (S n)),
  A ~= A' -> B ~= B' -> lda A B ~= lda A' B'.
Proof.
intros.
apply conv_trans with (lda A B').
apply conv_ldar.
  assumption.
apply conv_ldal.
  assumption.
Qed.

Lemma conv_subvar : forall (n : nat) (M N : term n), M ~= N ->
  forall (m : nat) (rho : fin n -> fin m), subvar M rho ~= subvar N rho.
Proof.
induction 1; intros.
 apply conv_par_red1.
   apply par_red1_subvar.
   assumption.
 apply conv_sym.
   auto.
 apply conv_trans with (subvar N rho); auto.
Qed.

Lemma conv_liftterm : forall (n : nat) (M N : term n), M ~= N ->
  liftterm M ~= liftterm N.
Proof.
intros.
unfold liftterm.
apply conv_subvar.
assumption.
Qed.

Definition conv_sub (m n : nat) (rho sigma : fin m -> term n) :=
  forall x, rho x ~= sigma x.
Implicit Arguments conv_sub [m n].
Notation "rho ~=s sigma" := (conv_sub rho sigma) (at level 80).

Lemma conv_sub_ref : forall m n (rho : fin m -> term n), rho ~=s rho.
Proof.
unfold conv_sub.
auto.
Qed.
Hint Resolve conv_sub_ref.

Lemma conv_liftsub : forall (m n : nat) (rho sigma : fin m -> term n),
  rho ~=s sigma -> liftsub rho ~=s liftsub sigma.
Proof.
unfold conv_sub.
destruct x; simpl.
 apply conv_liftterm.
   auto.
 apply conv_ref.
Qed.

Lemma conv_botsub : forall (n : nat) (M N : term n), M ~= N -> botsub M ~=s botsub N.
Proof.
unfold conv_sub.
destruct x; auto.
Qed.

Lemma conv_substl : forall (n : nat) (M N : term n), conv M N ->
  forall (m : nat) (rho : fin n -> term m),
  subst M rho ~= subst N rho.
Proof.
induction 1; intros.
 apply conv_par_red1.
   apply par_red1_subst; auto.
 apply conv_sym.
   auto.
 apply conv_trans with (subst N rho); auto.
Qed. 

Lemma conv_substr : forall (n : nat) (M : term n) (m : nat) (rho sigma : fin n -> term m),
  rho ~=s sigma -> subst M rho ~= subst M sigma.
Proof.
induction M; simpl; auto; intros.
(* Application *)
apply conv_app; auto.
(* Product *)
apply conv_pi.
 auto.
 apply IHM2.
   apply conv_liftsub.
   assumption.
(* Abstraction *)
apply conv_lda.
 auto.
 apply IHM2.
   apply conv_liftsub.
   assumption.
Qed.

Lemma conv_subst : forall (m n : nat) (M N : term m) (rho sigma : fin m -> term n),
  M ~= N -> rho ~=s sigma -> subst M rho ~= subst N sigma.
Proof.
intros.
apply conv_trans with (subst M sigma).
apply conv_substr.
  assumption.
apply conv_substl.
  assumption.
Qed.

Lemma conv_subbotl : forall n (M N : term (S n)) P, M ~= N -> subbot M P ~= subbot N P.
Proof.
intros.
unfold subbot.
apply conv_substl.
assumption.
Qed.

Lemma conv_subbotr : forall n (M : term (S n)) P Q,
  P ~= Q -> subbot M P ~= subbot M Q.
Proof.
intros.
unfold subbot.
apply conv_substr.
apply conv_botsub.
assumption.
Qed.

Lemma conv_subbot : forall (n : nat) (M N : term (S n)) (P Q : term n),
  M ~= N -> P ~= Q -> subbot M P ~= subbot N Q.
Proof.
intros.
unfold subbot.
apply conv_subst.
assumption.
apply conv_botsub.
assumption.
Qed.
