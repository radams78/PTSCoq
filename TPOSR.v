Require Import Finite.
Require Import Terms.
Require Import Labterms.
Require Import PTS.
Require Import PTSeq.

Inductive TPOSR : forall n : nat, lab_ctxt n -> option (lab_term n * lab_term n * lab_term n) -> Prop :=
  TPOSR_emp    : TPOSR 0 tt None |
  TPOSR_ctxt   : forall (n : nat) (Theta : lab_ctxt n) (A A' : lab_term n) (s : sort),
           TPOSR _ Theta (Some (A, A', lab_srt s)) ->
	   TPOSR (S n) (Theta, A) None |
  TPOSR_var    : forall (n : nat) (Theta : lab_ctxt n) (x : fin n),
           TPOSR _ Theta None ->
           TPOSR _ Theta (Some (lab_var x, lab_var x, lab_typeof x Theta)) |
  TPOSR_ax     : forall (n : nat) (Theta : lab_ctxt n) (s t : sort),
           axiom s t ->
           TPOSR _ Theta None ->
           TPOSR _ Theta (Some (lab_srt s, lab_srt s, lab_srt t)) |
  TPOSR_prod   : forall (n : nat) (Theta : lab_ctxt n) (A A' : lab_term n) (B B' : lab_term (S n)) (s1 s2 s3 : sort),
           rule s1 s2 s3 ->
	   TPOSR _ Theta (Some (A, A', lab_srt s1)) ->
	   TPOSR (S n) (Theta, A) (Some (B, B', lab_srt s2)) ->
	   TPOSR _ Theta (Some (lab_pi A B, lab_pi A' B', lab_srt s3)) |
  TPOSR_lambda : forall (n : nat) (Theta : lab_ctxt n) (A A' : lab_term n) (B B' M M' : lab_term (S n)) (s1 s2 s3 : sort),
           rule s1 s2 s3 ->
	   TPOSR (S n) (Theta, A) (Some (M, M', B)) ->
	   TPOSR _ Theta (Some (A, A', lab_srt s1)) ->
	   TPOSR (S n) (Theta, A) (Some (B, B', lab_srt s2)) ->
	   TPOSR _ Theta (Some (lab_lda A M, lab_lda A' M', lab_pi A B)) |
  TPOSR_app    : forall (n : nat) (Theta : lab_ctxt n) (A A' M M' N N' : lab_term n) (B B' : lab_term (S n)) (s1 s2 s3 : sort),
           rule s1 s2 s3 ->
	   TPOSR _ Theta (Some (M, M', lab_pi A B)) ->
	   TPOSR _ Theta (Some (N, N', A)) ->
	   TPOSR _ Theta (Some (A, A', lab_srt s1)) ->
	   TPOSR (S n) (Theta, A) (Some (B, B', lab_srt s2)) ->
	   TPOSR _ Theta (Some (lab_app B M N, lab_app B' M' N', lab_subbot B N)) |
  TPOSR_beta   : forall (n : nat) (Theta : lab_ctxt n) (A A' N N' : lab_term n) (B B' M M' : lab_term (S n)) (s1 s2 s3 : sort),
           rule s1 s2 s3 ->
	   TPOSR _ Theta (Some (A, A', lab_srt s1)) ->
	   TPOSR (S n) (Theta, A) (Some (B, B', lab_srt s2)) ->
	   TPOSR (S n) (Theta, A) (Some (M, M', B)) ->
	   TPOSR _ Theta (Some (N, N', A)) ->
	   TPOSR _ Theta (Some (lab_app B (lab_lda A M) N, lab_subbot M' N', lab_subbot B N)) |
  TPOSR_red    : forall (n : nat) (Theta : lab_ctxt n) (M N A B : lab_term n) (s : sort),
           TPOSR _ Theta (Some (M, N, A)) ->
	   TPOSR _ Theta (Some (A, B, lab_srt s)) ->
	   TPOSR _ Theta (Some (M, N, B)) |
  TPOSR_exp    : forall (n : nat) (Theta : lab_ctxt n) (M N A B : lab_term n) (s : sort),
           TPOSR _ Theta (Some (M, N, B)) ->
	   TPOSR _ Theta (Some (A, B, lab_srt s)) ->
	   TPOSR _ Theta (Some (M, N, A)).

Implicit Arguments TPOSR [n].

Definition TPOSR_valid (n : nat) (Theta : lab_ctxt n) := TPOSR Theta None.

Implicit Arguments TPOSR_valid [n].

Definition TPOSR' (n : nat) (Theta : lab_ctxt n) (M N A : lab_term n) := TPOSR Theta (Some (M,N,A)).

Implicit Arguments TPOSR' [n].

Inductive TPOSRplus (n : nat) (Theta : lab_ctxt n) (Z : lab_term n) : lab_term n -> lab_term n -> Prop :=
  TPOSRplus_TPOSR' : forall (X Y : lab_term n), TPOSR' Theta X Y Z -> TPOSRplus _ Theta Z X Y |
  TPOSRplus_trans : forall (W X Y : lab_term n), TPOSRplus _ Theta Z W X -> TPOSRplus _ Theta Z X Y -> TPOSRplus _ Theta Z W Y.

Implicit Arguments TPOSRplus [n].

Inductive TPOSRconv (n : nat) (Theta : lab_ctxt n) (s : sort) : lab_term n -> lab_term n -> Prop :=
  TPOSRconv_TPOSR' : forall (X Y : lab_term n), TPOSR' Theta X Y (lab_srt s) -> TPOSRconv _ Theta s X Y |
  TPOSRconv_sym    : forall (X Y : lab_term n), TPOSRconv _ Theta s X Y -> TPOSRconv _ Theta s Y X |
  TPOSRconv_trans  : forall (X Y Z : lab_term n), TPOSRconv _ Theta s X Y -> TPOSRconv _ Theta s Y Z -> TPOSRconv _ Theta s X Z.

Implicit Arguments TPOSRconv [n].

Lemma pre_TPOSR_conv : forall (n : nat) (Theta : lab_ctxt n) (s : sort) (A B : lab_term n), TPOSRconv Theta s A B ->
  forall (M N : lab_term n), TPOSR' Theta M N A <-> TPOSR' Theta M N B.
  induction 1; intros.
  unfold TPOSR'.
    split; intro.
    apply TPOSR_red with X s; assumption.
    apply TPOSR_exp with Y s; assumption.
  apply iff_sym.
    apply IHTPOSRconv.
  apply iff_trans with (TPOSR' Theta M N Y).
    apply IHTPOSRconv1.
    apply IHTPOSRconv2.
Save.

Lemma TPOSR_conv : forall (n : nat) (Theta : lab_ctxt n) (M N A B : lab_term n) (s : sort),
  TPOSR' Theta M N A -> TPOSRconv Theta s A B -> TPOSR' Theta M N B.
  intros.
  elim pre_TPOSR_conv with n Theta s A B M N; auto.
Save.

Theorem TPOSR_to_PTSeq : forall (n : nat) (Theta : lab_ctxt n) (X : option (lab_term n * lab_term n * lab_term n)), TPOSR Theta X ->
  (X = None -> (forall (s t : sort), axiom s t -> PTS' (unlab_ctxt Theta) (srt s) (srt t))
            /\ (forall (x : fin n), PTS' (unlab_ctxt Theta) x (unlab (lab_typeof x Theta)))) /\
  forall (M N A : lab_term n), X = Some (M,N,A) -> PTSeq' (unlab_ctxt Theta) (unlab M) (unlab N) (unlab A).
  induction 1; simpl; split; try discriminate 1.
  split.
    exact ax.
    intro x.
      case x.
  split.
    intros.
    unfold PTS'.
    apply weak with (M := srt (n := n) s0) (A := srt (n := n) t) (s := s).
