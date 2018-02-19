Require Export PTS.

Inductive lab_term : nat -> Set :=
  lab_var :> forall n : nat, fin n -> lab_term n |
  lab_srt : forall n : nat, sort -> lab_term n |
  lab_lda : forall n : nat, lab_term n -> lab_term (S n) -> lab_term n |
  lab_pi  : forall n : nat, lab_term n -> lab_term (S n) -> lab_term n |
  lab_app : forall n : nat, lab_term (S n) -> lab_term n -> lab_term n -> lab_term n.

Implicit Arguments lab_var [n].
Implicit Arguments lab_srt [n].
Implicit Arguments lab_lda [n].
Implicit Arguments lab_pi [n].
Implicit Arguments lab_app [n].

Definition lab_subvar : forall m : nat, lab_term m -> forall n : nat, (fin m -> fin n) -> lab_term n.
  induction 1.
  intros m rho.
    exact (rho f).
  intros.
    exact (lab_srt s).
  intros m rho.
    exact (lab_lda (IHlab_term1 m rho) (IHlab_term2 (S m) (Sfun rho))).
  intros m rho.
    exact (lab_pi (IHlab_term1 m rho) (IHlab_term2 (S m) (Sfun rho))).
  intros m rho.
    exact (lab_app (IHlab_term1 (S m) (Sfun rho)) (IHlab_term2 m rho) (IHlab_term3 m rho)).
Defined.

Implicit Arguments lab_subvar [m n].

Definition liftlabterm (n : nat) (M : lab_term n) : lab_term (S n) := (lab_subvar M (up (n:=n))).

Implicit Arguments liftlabterm [n].

Definition liftlabsub (m n : nat) (rho : fin m -> lab_term n) (x : fin (S m)) : lab_term (S n) :=
  match x with
    None => bot |
    Some y => liftlabterm (rho y)
  end.

Implicit Arguments liftlabsub [m n].

Definition lab_subst : forall m : nat, lab_term m -> forall n : nat, (fin m -> lab_term n) -> lab_term n.
  induction 1.
  intros m rho.
    exact (rho f).
  intros m rho.
    exact (lab_srt s).
  intros m rho.
    exact (lab_lda (IHlab_term1 _ rho) (IHlab_term2 (S m) (liftlabsub rho))).
  intros m rho.
    exact (lab_pi (IHlab_term1 _ rho) (IHlab_term2 (S m) (liftlabsub rho))).
  intros m rho.
    exact (lab_app (IHlab_term1 (S m) (liftlabsub rho)) (IHlab_term2 _ rho) (IHlab_term3 _ rho)).
Defined.

Implicit Arguments lab_subst [m n].

Definition lab_subbot (n : nat) (M : lab_term (S n)) (N : lab_term n) : lab_term n :=
  lab_subst M (fun x : fin (S n) =>
    match x with
      None => N |
      Some y => lab_var y
    end).

Implicit Arguments lab_subbot [n].

Definition unlab : forall n : nat, lab_term n -> term n.
  induction 1.
  exact f.
  exact (srt s).
  exact (lda IHlab_term1 IHlab_term2).
  exact (pi IHlab_term1 IHlab_term2).
  exact (app IHlab_term2 IHlab_term3).
Defined.

Implicit Arguments unlab [n].

Lemma unlab_var : forall (n : nat) (x : fin n) (M : lab_term n), unlab M = x -> M = x.
  induction M; try discriminate 1.
  simpl.
  intro.
  rewrite var_inj with n f x.
  reflexivity.
  assumption.
Save.

Lemma unlab_srt : forall (n : nat) (s : sort) (M : lab_term n), unlab M = srt s -> M = lab_srt s.
  intros n s M.
  case M; try discriminate 1.
  intros.
  rewrite srt_inj with n0 s0 s.
  reflexivity.
  assumption.
Save.

Lemma unlab_lda : forall (n : nat) (M : lab_term n) (A : term n) (N : term (S n)),
  unlab M = lda A N ->
  exists A' : lab_term n, exists N' : lab_term (S n),
  M = lab_lda A' N' /\ unlab A' = A /\ unlab N' = N.
  intros n M.
  case M; try discriminate 1.
  intros m A' N' A N H.
  split with A'.
  split with N'.
  split.
  reflexivity.
  split.
  apply lda_injl with (unlab N') N.
    assumption.
  apply lda_injr with (unlab A') A.
    assumption.
Save.

Lemma unlab_pi : forall (n : nat) (M : lab_term n) (A : term n) (N : term (S n)),
  unlab M = pi A N ->
  exists A' : lab_term n, exists N' : lab_term (S n),
  M = lab_pi A' N' /\ unlab A' = A /\ unlab N' = N.
  intros n M.
  case M; try discriminate 1.
  intros m A' N' A N H.
  split with A'.
  split with N'.
  split.
  reflexivity.
  split.
  apply pi_injl with (unlab N') N.
    assumption.
  apply pi_injr with (unlab A') A.
    assumption.
Save.

Lemma unlab_app : forall (n : nat) (M : lab_term n) (N P : term n),
  unlab M = app N P ->
  exists B' : lab_term (S n), exists N' : lab_term n, exists P' : lab_term n,
  M = lab_app B' N' P' /\ unlab N' = N /\ unlab P' = P.
  intros n M.
  case M; try discriminate 1.
  clear n M.
  intros n B' N' P' N P H.
  split with B'.
  split with N'.
  split with P'.
  split.
  reflexivity.
  split.
  apply app_injl with (unlab P') P.
    assumption.
  apply app_injr with (unlab N') N.
    assumption.
Save.

Lemma unlab_subvar : forall (m : nat) (M : lab_term m) (n : nat) (rho : fin m -> fin n), unlab (lab_subvar M rho) = subvar (unlab M) rho.
  induction M; auto; simpl.
  intros.
    rewrite IHM1.
    rewrite IHM2.
    reflexivity.
  intros.
    rewrite IHM1.
    rewrite IHM2.
    reflexivity.
  intros.
    rewrite IHM2.
    rewrite IHM3.
    reflexivity.
Save.

Lemma unlab_lift : forall (n : nat) (M : lab_term n), unlab (liftlabterm M) = liftterm (unlab M).
  intros.
  unfold liftlabterm. 
  unfold liftterm.
  apply unlab_subvar.
Save.

Lemma unlab_liftsub : forall (m n : nat) (rho : fin m -> lab_term n) (x : fin (S m)),
   unlab (liftlabsub rho x) = liftsub (fun x0 : fin m => unlab (rho x0)) x.
  unfold liftlabsub.
  unfold liftsub.
  intros.
  case x; simpl.
  intro f.
    apply unlab_lift.
  reflexivity.
Save.

Lemma unlab_subst : forall (m : nat) (M : lab_term m) (n : nat) (rho : fin m -> lab_term n), unlab (lab_subst M rho) = subst (unlab M) (fun x : fin m => unlab (rho x)).
  induction M; simpl.
  reflexivity.
  reflexivity.
  intros.
    rewrite IHM1.
    rewrite IHM2.
    apply lda_wd.
    reflexivity.
    apply subst_ext.
    apply unlab_liftsub.
  intros.
    rewrite IHM1.
    rewrite IHM2.
    apply pi_wd.
    reflexivity.
    apply subst_ext.
    apply unlab_liftsub.
  intros.
    rewrite IHM2.
    rewrite IHM3.
    reflexivity.
Save.

Lemma unlab_subbot : forall (n : nat) (M : lab_term (S n)) (N : lab_term n),
  unlab (lab_subbot M N) = subbot (unlab M) (unlab N).
  unfold lab_subbot.
  unfold subbot.
  intros.
  rewrite unlab_subst.
  apply subst_ext.
  intro x.
  case x; reflexivity.
Save.

Fixpoint lab_ctxt (n : nat) {struct n} : Set :=
  match n with
    O => unit |
    (S m) => (prod (lab_ctxt m) (lab_term m))
  end.

Definition lab_typeof : forall (n : nat), fin n -> lab_ctxt n -> lab_term n.
  induction n; simpl; intros x Theta; destruct x; destruct Theta.
  exact (liftlabterm (IHn f l)).
  exact (liftlabterm l0).
Defined.

Implicit Arguments lab_typeof [n].

Definition unlab_ctxt : forall n : nat, lab_ctxt n -> context n.
  induction n; simpl.
  split.
  induction 1.
    split.
    exact (IHn a).
    exact (unlab b).
Defined.

Implicit Arguments unlab_ctxt [n].

Inductive lab_par_red1 : forall n : nat, lab_term n -> lab_term n -> Prop :=
  lab_par_red1_var : forall n : nat, forall x : fin n, lab_par_red1 _ x x |
  lab_par_red1_srt : forall n : nat, forall s : sort, lab_par_red1 n (lab_srt s) (lab_srt s) |
  lab_par_red1_lda : forall n : nat, forall A A' : lab_term n, forall M M' : lab_term (S n),
    lab_par_red1 _ A A' -> lab_par_red1 _ M M' -> lab_par_red1 _ (lab_lda A M) (lab_lda A' M') |
  lab_par_red1_pi  : forall n : nat, forall A A' : lab_term n, forall B B' : lab_term (S n),
    lab_par_red1 _ A A' -> lab_par_red1 _ B B' -> lab_par_red1 _ (lab_pi A B) (lab_pi A' B') |
  lab_par_red1_app : forall n : nat, forall B B' : lab_term (S n), forall M M' N N' : lab_term n, lab_par_red1 _ B B' -> lab_par_red1 _ M M' -> lab_par_red1 _ N N' ->
    lab_par_red1 _ (lab_app B M N) (lab_app B' M' N') |
  lab_par_red1_beta : forall n : nat, forall A N N' : lab_term n, forall B M M' : lab_term (S n), lab_par_red1 _ M M' -> lab_par_red1 _ N N' ->
    lab_par_red1 _ (lab_app B (lab_lda A M) N) (lab_subbot M' N').

Implicit Arguments lab_par_red1 [n].

Lemma lab_par_red1_ref : forall (n : nat) (M : lab_term n), lab_par_red1 M M.
  induction M.
  apply lab_par_red1_var.
  apply lab_par_red1_srt.
  apply lab_par_red1_lda; assumption.
  apply lab_par_red1_pi; assumption.
  apply lab_par_red1_app; assumption.
Save.

Lemma unlab_par_red1 : forall (n : nat) (M N : lab_term n), lab_par_red1 M N -> par_red1 (unlab M) (unlab N).
  induction 1; simpl.
  apply par_red1_var.
  apply par_red1_srt.
  apply par_red1_lda; assumption.
  apply par_red1_pi; assumption.
  apply par_red1_app; assumption.
  rewrite unlab_subbot.
    apply par_red1_beta; assumption.
Save.

Lemma pre_unlab_par_red1' : forall (n : nat) (M N : term n), par_red1 M N ->
  forall Ml : lab_term n, unlab Ml = M ->
  exists Nl : lab_term n, lab_par_red1 Ml Nl /\ unlab Nl = N.
  induction 1; intros Pl H1.
  split with (lab_var x).
    split.
    rewrite unlab_var with n x Pl.
      apply lab_par_red1_var.
      assumption.
    reflexivity.
  split with (lab_srt (n:=n) s).
    split.
    rewrite unlab_srt with n s Pl.
      apply lab_par_red1_srt.
      assumption.
    reflexivity.
  elim unlab_app with n Pl M N.
    intros Bl H2.
    elim H2.
    clear H2.
    intros Ml H2.
    elim H2.
    clear H2.
    intros Nl H2.
    destruct H2.
    destruct H3.
    elim IHpar_red1_1 with Ml.
      intros M'l H5.
      destruct H5.
      elim IHpar_red1_2 with Nl.
        intros N'l H7.
	destruct H7.
	split with (lab_app Bl M'l N'l).
	split.
	rewrite H2.
	  apply lab_par_red1_app; try assumption.
	  apply lab_par_red1_ref.
	simpl.
	  apply app_wd; assumption.
	assumption.
      assumption.
    assumption.
  elim unlab_pi with n Pl A B.
    intros Al H2.
    elim H2.
    clear H2.
    intros Bl H2.
    destruct H2.
    destruct H3.
    elim IHpar_red1_1 with Al.
      intros A'l H5.
      destruct H5.
      elim IHpar_red1_2 with Bl.
	intros B'l H7.
	destruct H7.
	split with (lab_pi A'l B'l).
	split.
	rewrite H2.
	  apply lab_par_red1_pi; assumption.
	simpl.
	  apply pi_wd; assumption.
	assumption.
      assumption.
    assumption.
  elim unlab_lda with n Pl A M.
    intros Al H2.
    elim H2.
    clear H2.
    intros Ml H2.
    destruct H2.
    destruct H3.
    elim IHpar_red1_1 with Al.
      intros A'l H5.
      destruct H5.
      elim IHpar_red1_2 with Ml.
	intros M'l H7.
	destruct H7.
	split with (lab_lda A'l M'l).
	split.
	rewrite H2.
	  apply lab_par_red1_lda; assumption.
	simpl.
	  apply lda_wd; assumption.
	assumption.
      assumption.
    assumption.
  elim unlab_app with n Pl (lda A M) N.
    intros Bl H2.
    elim H2.
    clear H2.
    intros Ql H2.
    elim H2.
    clear H2.
    intros Nl H2.
    destruct H2.
    destruct H3.
    elim unlab_lda with n Ql A M.
      intros Al H5.
      elim H5.
      clear H5.
      intros Ml H5.
      destruct H5.
      destruct H6.
      elim IHpar_red1_1 with Ml.
	intros M'l H8.
	destruct H8.
	elim IHpar_red1_2 with Nl.
	  intros N'l H10.
	  destruct H10.
	  split with (lab_subbot M'l N'l).
	  split.
	  rewrite H2.
	    rewrite H5.
	    apply lab_par_red1_beta; assumption.
	  rewrite unlab_subbot.
	    rewrite H9.
	    rewrite H11.
	    reflexivity.
	  assumption.
	assumption.
      assumption.
    assumption.
Save.

Lemma unlab_par_red1' : forall (n : nat) (Ml : lab_term n) (N : term n), par_red1 (unlab Ml) N ->
  exists Nl : lab_term n, lab_par_red1 Ml Nl /\ unlab Nl = N.
  intros.
  apply pre_unlab_par_red1' with (unlab Ml); auto.
Save.

Inductive lab_red : forall n : nat, lab_term n -> lab_term n -> Prop :=
  lab_red_par_red1 : forall (n : nat) (M N : lab_term n), lab_par_red1 M N -> lab_red _ M N |
  lab_red_trans : forall (n : nat) (M N P : lab_term n), lab_red _ M N -> lab_red _ N P -> lab_red _ M P.

Implicit Arguments lab_red [n].

Lemma unlab_red : forall (n : nat) (M N : lab_term n), lab_red M N -> red (unlab M) (unlab N).
  induction 1.
  apply red_par_red1.
    apply unlab_par_red1.
    assumption.
  apply red_trans with (unlab N); assumption.
Save.

Lemma pre_unlab_red' : forall (n : nat) (M N : term n), red M N ->
  forall Ml : lab_term n, unlab Ml = M ->
  exists Nl : lab_term n, lab_red Ml Nl /\ unlab Nl = N.
  induction 1; intros.
  elim pre_unlab_par_red1' with n M N Ml; try assumption.
    intros Nl H1.
    destruct H1.
    split with Nl.
    split.
    apply lab_red_par_red1.
      assumption.
    assumption.
  elim IHred1 with Ml.
    intros Nl H2.
    destruct H2.
    elim IHred2 with Nl.
      intros Pl H4.
      destruct H4.
      split with Pl.
      split.
      apply lab_red_trans with Nl; assumption.
      assumption.
    assumption.
  assumption.
Save.

Lemma unlab_red' : forall (n : nat) (Ml : lab_term n) (N : term n), red (unlab Ml) N ->
  exists Nl : lab_term n, lab_red Ml Nl /\ unlab Nl = N.
  intros.
  apply pre_unlab_red' with (unlab Ml); auto.
Save.

Inductive lab_conv : forall n : nat, lab_term n -> lab_term n -> Prop :=
  lab_conv_par_red1 : forall (n : nat) (M N : lab_term n), lab_par_red1 M N -> lab_conv _ M N |
  lab_conv_sym : forall (n : nat) (M N : lab_term n), lab_conv _ M N -> lab_conv _ N M |
  lab_conv_trans : forall (n : nat) (M N P : lab_term n), lab_conv _ M N -> lab_conv _ N P -> lab_conv _ M P.

Implicit Arguments lab_conv [n].

Lemma unlab_conv : forall (n : nat) (M N : lab_term n), lab_conv M N -> conv (unlab M) (unlab N).
  induction 1.
  apply conv_par_red1.
    apply unlab_par_red1.
    assumption.
  apply conv_sym.
    assumption.
  apply conv_trans with (unlab N); assumption.
Save.
