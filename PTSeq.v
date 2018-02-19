Require Export PTS.

Inductive PTS' : forall n : nat, context n -> term n -> term n -> Prop :=

  ax : forall (s t : sort), axiom s t ->
    PTS' O tt (srt s) (srt t) |

  var : forall (n : nat) (Gamma : context n) (A : term n) (s : sort),
    PTS' _ Gamma A (srt s) ->
    PTS' (S n) (Gamma, A) bot (liftterm A) |

  weak : forall (n : nat) (Gamma : context n) (M A B : term n) (s : sort),
    PTS' _ Gamma M A ->
    PTS' _ Gamma B (srt s) ->
    PTS' (S n) (Gamma, B) (liftterm M) (liftterm A) |

  prod : forall (n : nat) (Gamma : context n) (A : term n) (B : term (S n)) (s1 s2 s3 : sort), rule s1 s2 s3 ->
    PTS' _ Gamma A (srt s1) ->
    PTS' (S n) (Gamma, A) B (srt s2) ->
    PTS' _ Gamma (pi A B) (srt s3) |

  lambda : forall (n : nat) (Gamma : context n) (A : term n) (M B : term (S n)) (s1 s2 s3 : sort), rule s1 s2 s3 ->
    PTS' _ Gamma A (srt s1) ->
    PTS' (S n) (Gamma, A) M B ->
    PTS' (S n) (Gamma, A) B (srt s2) ->
    PTS' _ Gamma (lda A M) (pi A B) |

  appl : forall (n : nat) (Gamma : context n) (M N A : term n) (B : term (S n)),
    PTS' _ Gamma M (pi A B) ->
    PTS' _ Gamma N A ->
    PTS' _ Gamma (app M N) (subbot B N) |

  conv : forall (n : nat) (Gamma : context n) (M A B : term n) (s : sort),
    PTS' _ Gamma M A ->
    PTSeq _ Gamma A B (srt s) ->
    PTS' _ Gamma M B

with PTSeq : forall n : nat, context n -> term n -> term n -> term n -> Prop :=

  weak_eq : forall (n : nat) (Gamma : context n) (M N A B : term n) (s : sort),
    PTSeq _ Gamma M N A ->
    PTS' _ Gamma B (srt s) ->
    PTSeq (S n) (Gamma, B) (liftterm M) (liftterm N) (liftterm A) |

  prod_eq : forall (n : nat) (Gamma : context n) (A A' : term n) (B B' : term (S n)) (s1 s2 s3 : sort), rule s1 s2 s3 ->
    PTSeq _ Gamma A A' (srt s1) ->
    PTS'  _ Gamma A (srt s1) ->
    PTSeq (S n) (Gamma, A) B B' (srt s2) ->
    PTSeq _ Gamma (pi A B) (pi A' B') (srt s3) |

  lambda_eq : forall (n : nat) (Gamma : context n) (A A' : term n) (M M' B : term (S n)) (s1 s2 s3 : sort), rule s1 s2 s3 ->
    PTSeq (S n) (Gamma, A) M M' B ->
    PTSeq _ Gamma A A' (srt s1) ->
    PTS' _ Gamma A (srt s1) ->
    PTS' (S n) (Gamma, A) B (srt s2) ->
    PTSeq _ Gamma (lda A M) (lda A' M') (pi A B) |

  app_eq : forall (n : nat) (Gamma : context n) (M M' N N' A : term n) (B : term (S n)),
    PTSeq _ Gamma M M' (pi A B) ->
    PTSeq _ Gamma N N' A ->
    PTSeq _ Gamma (app M N) (app M' N') (subbot B N) |

  ref : forall (n : nat) (Gamma : context n) (M A : term n),
    PTS' _ Gamma M A ->
    PTSeq _ Gamma M M A |

  sym : forall (n : nat) (Gamma : context n) (M N A : term n),
    PTSeq _ Gamma M N A ->
    PTSeq _ Gamma N M A |

  trans : forall (n : nat) (Gamma : context n) (M N P A : term n),
    PTSeq _ Gamma M N A ->
    PTSeq _ Gamma N P A ->
    PTSeq _ Gamma M P A |

  conv_eq : forall (n : nat) (Gamma : context n) (M N A B : term n) (s : sort),
    PTSeq _ Gamma M N A ->
    PTSeq _ Gamma A B (srt s) ->
    PTSeq _ Gamma M N B |

  beta : forall (n : nat) (Gamma : context n) (M A : term n) (N B : term (S n)) (s1 s2 s3 : sort), rule s1 s2 s3 ->
    PTS' (S n) (Gamma, A) N B ->
    PTS' _ Gamma M A ->
    PTS' _ Gamma A (srt s1) ->
    PTS' (S n) (Gamma, A) B (srt s2) ->
    PTSeq _ Gamma (app (lda A N) M) (subbot N M) (subbot B M).

Notation "Gamma |-- M ; A" := (PTS' _ Gamma M A) (at level 70).
Notation "Gamma |-- M == N ; A" := (PTSeq _ Gamma M N A) (at level 70).

Scheme PTS'_ind' := Minimality for PTS' Sort Prop
with PTSeq_ind' := Minimality for PTSeq Sort Prop.

(* The schema for proving propositions by simultaneous induction over these two relations. *)
(* As far as I know, this needs to be built by hand. *)

Theorem PTSeq_induction : forall (P  : forall n : nat, context n -> term n -> term n -> Prop)
                                 (P0 : forall n : nat, context n -> term n -> term n -> term n -> Prop),
       (forall s t, axiom s t -> P 0 tt (srt s) (srt t)) ->
       (forall n Gamma A s,
        Gamma |-- A ; srt s ->
        P n Gamma A (srt s) -> P (S n) (Gamma, A) (bot (n:=n)) (liftterm A)) ->
       (forall n Gamma M A B s,
        Gamma |-- M ; A ->
        P n Gamma M A ->
        Gamma |-- B ; srt s ->
        P n Gamma B (srt s) -> P (S n) (Gamma, B) (liftterm M) (liftterm A)) ->
       (forall n Gamma A B s1 s2 s3,
        rule s1 s2 s3 ->
        Gamma |-- A ; srt s1 ->
        P n Gamma A (srt s1) ->
        ((Gamma, A) : context (S n)) |--  B ; srt s2 ->
        P (S n) (Gamma, A) B (srt s2) -> P n Gamma (pi A B) (srt s3)) ->
       (forall n Gamma A M B s1 s2 s3,
        rule s1 s2 s3 ->
        Gamma |-- A ; srt s1 ->
        P n Gamma A (srt s1) ->
        ((Gamma, A) : context (S n)) |-- M ; B ->
        P (S n) (Gamma, A) M B ->
        ((Gamma, A) : context (S n)) |-- B ; srt s2 ->
        P (S n) (Gamma, A) B (srt s2) -> P n Gamma (lda A M) (pi A B)) ->
       (forall n Gamma M N A B,
        Gamma |-- M ; pi A B ->
        P n Gamma M (pi A B) ->
        Gamma |-- N ; A -> P n Gamma N A -> P n Gamma (app M N) (subbot B N)) ->
       (forall n Gamma M A B s,
        Gamma |-- M ; A ->
        P n Gamma M A ->
        Gamma |-- A == B ; srt s -> P0 n Gamma A B (srt s) -> P n Gamma M B) ->
       (forall n Gamma M N A B s,
        Gamma |-- M == N ; A ->
        P0 n Gamma M N A ->
        Gamma |-- B ; srt s ->
        P n Gamma B (srt s) ->
        P0 (S n) (Gamma, B) (liftterm M) (liftterm N) (liftterm A)) ->
       (forall n Gamma A A' B B' s1 s2 s3,
        rule s1 s2 s3 ->
        Gamma |-- A == A' ; srt s1 ->
        P0 n Gamma A A' (srt s1) ->
	Gamma |-- A ; srt s1 ->
	P n Gamma A (srt s1) ->
        ((Gamma, A) : context (S n)) |--  B == B' ; srt s2 ->
        P0 (S n) (Gamma, A) B B' (srt s2) ->
        P0 n Gamma (pi A B) (pi A' B') (srt s3)) ->
       (forall n Gamma A A' M M' B s1 s2 s3,
        rule s1 s2 s3 ->
        ((Gamma, A) : context (S n)) |-- M == M' ; B ->
        P0 (S n) (Gamma, A) M M' B ->
        Gamma |-- A == A' ; srt s1 ->
        P0 n Gamma A A' (srt s1) ->
	Gamma |-- A ; srt s1 ->
	P n Gamma A (srt s1) ->
        ((Gamma, A) : context (S n)) |--  B ; srt s2 ->
        P (S n) (Gamma, A) B (srt s2) ->
        P0 n Gamma (lda A M) (lda A' M') (pi A B)) ->
       (forall n Gamma M M' N N' A B,
        Gamma |-- M == M' ; pi A B ->
        P0 n Gamma M M' (pi A B) ->
        Gamma |-- N == N' ; A ->
        P0 n Gamma N N' A -> P0 n Gamma (app M N) (app M' N') (subbot B N)) ->
       (forall n Gamma M A,
        Gamma |-- M ; A -> P n Gamma M A -> P0 n Gamma M M A) ->
       (forall n Gamma M N A,
        Gamma |-- M == N ; A -> P0 n Gamma M N A -> P0 n Gamma N M A) ->
       (forall n Gamma M N P A,
        Gamma |-- M == N ; A ->
        P0 n Gamma M N A ->
        Gamma |-- N == P ; A -> P0 n Gamma N P A -> P0 n Gamma M P A) ->
       (forall n Gamma M N A B s,
        Gamma |-- M == N ; A ->
        P0 n Gamma M N A ->
        Gamma |-- A == B ; srt s -> P0 n Gamma A B (srt s) -> P0 n Gamma M N B) ->
       (forall n Gamma M A N B s1 s2 s3,
        rule s1 s2 s3 ->
        ((Gamma, A) : context (S n)) |--  N ; B ->
        P (S n) (Gamma, A) N B ->
        Gamma |-- M ; A ->
        P n Gamma M A ->
        Gamma |-- A ; srt s1 ->
        P n Gamma A (srt s1) ->
        ((Gamma, A) : context (S n)) |--  B ; srt s2 ->
        P (S n) (Gamma, A) B (srt s2) ->
        P0 n Gamma (app (lda A N) M) (subbot N M) (subbot B M)) ->
       (forall n Gamma M A,
        Gamma |-- M ; A -> P n Gamma M A) /\
        forall n Gamma M N A,
        Gamma |-- M == N ; A -> P0 n Gamma M N A.
Proof.
split.
apply PTS'_ind' with P0; assumption.
apply PTSeq_ind' with P; assumption.
Qed.

Definition ctxt_eq : forall n : nat, context n -> context n -> Prop.
induction n; simpl.
intros _ _.
  exact True.
destruct 1.
  destruct 1.
  exact (IHn c c0 /\ exists s : sort, c |-- t == t0 ;srt s /\ c0 |-- t == t0 ;srt s).
Defined.
Notation "Gamma ==c Delta" := (ctxt_eq _ Gamma Delta) (at level 70).

Definition valid' : forall n : nat, context n -> Prop.
induction n; simpl.
intros _.
  exact True.
destruct 1.
  exact (exists s : sort, c |-- t ; srt s).
Defined.

Implicit Arguments valid' [n].

Theorem Context_Validity : (forall n (Gamma : context n) M A, Gamma |-- M ; A -> valid' Gamma)
                        /\ (forall n (Gamma : context n) M N A, Gamma |-- M == N ; A -> valid' Gamma).
Proof.
apply PTSeq_induction with (P := fun (n : nat) (Gamma : context n) (M A : term n) => valid' Gamma)
  (P0 := fun (n : nat) (Gamma : context n) (M N A : term n) => valid' Gamma); simpl; try split; auto; intros; split with s; assumption.
Qed.

Theorem PTS'_Context_Validity : forall n (Gamma : context n) M A, Gamma |-- M ; A -> valid' Gamma.
Proof.
elim Context_Validity.
auto.
Qed.

Theorem PTSeq_Context_Validity : forall n (Gamma : context n) M N A, Gamma |-- M == N ; A -> valid' Gamma.
Proof.
elim Context_Validity.
auto.
Qed.

Theorem ctxt_eq_ref : forall n (Gamma : context n), valid' Gamma -> Gamma ==c Gamma.
Proof.
induction n; simpl.
 auto.
 destruct Gamma.
   rename c into Gamma.
   rename t into A.
   destruct 1.
   rename x into s.
   split.
    apply IHn.
      apply PTS'_Context_Validity with A (srt (n:=n) s).
      assumption.
    split with s.
      split; apply ref; assumption.
Qed.

Theorem pre_Context_Conversion :
  (forall n (Gamma : context n) M A, Gamma |-- M ; A ->
    forall Delta, Gamma ==c Delta -> valid' Delta -> Delta |-- M ; A) /\
  (forall n (Gamma : context n) M N A, Gamma |-- M == N ; A ->
    forall Delta, Gamma ==c Delta -> valid' Delta -> Delta |-- M == N ; A).
Proof.
apply PTSeq_induction with
  (P := fun (n : nat) (Gamma : context n) (M A : term n) => forall (Delta : context n), Gamma ==c Delta -> valid' Delta -> Delta |-- M ; A)
  (P0 := fun (n : nat) (Gamma : context n) (M N A : term n) => forall (Delta : context n), Gamma ==c Delta -> valid' Delta -> Delta |-- M == N ; A);
  simpl.
(* ax *)
 destruct Delta.
   intros _ _.
   apply ax.
   assumption.
(* var *)
 destruct Delta.
   rename c into Delta.
   rename t into B.
   destruct 1.
   destruct H2.
   rename x into t.
   destruct H2.
   destruct 1.
   rename x into t'.
   apply conv with (liftterm B) t.
    apply var with t'.
      assumption.
    apply weak_eq with (s := t') (A := srt (n:=n) t).
      apply sym.
      assumption.
    assumption.
(* weak *)
  destruct Delta.
    rename c into Delta.
    rename t into C.
    destruct 1.
    destruct H4.
    rename x into t.
    destruct H4.
    destruct 1.
    rename x into t'.
    apply weak with t'.
     apply H0; auto.
       apply PTS'_Context_Validity with C (srt (n:=n) t').
       assumption.
     assumption.
(* prod *)
  intros.
    assert (Delta |-- A ; srt s1).
      auto.
    apply prod with s1 s2; auto.
    apply H3.
     split.
      assumption.
      split with s1.
        split; apply ref; assumption.
     split with s1.
       assumption.
(* lambda *)
  intros.
    assert (Delta |-- A ; srt s1).
      auto.
    assert (ctxt_eq (S n) (Gamma, A) (Delta, A)).
      split.
       assumption.
       split with s1.
         split; apply ref; auto.
    assert (exists s, Delta |-- A ; srt s).
      split with s1.
      assumption.
    apply lambda with s1 s2 s3; auto.
(* appl *)
  intros.
    apply appl with A; auto.
(* conv *)
  intros.
    apply conv with A s; auto.
(* weak_eq *)
  destruct Delta.
    rename c into Delta.
    rename t into C.
    destruct 1.
    destruct H4.
    rename x into t.
    destruct H4.
    destruct 1.
    rename x into t'.
    apply weak_eq with t'.
     apply H0; auto.
       apply PTS'_Context_Validity with C (srt (n:=n) t').
       assumption.
     assumption.
(* prod_eq *)
  intros.
    assert (Delta |-- A ; srt s1).
      auto.
    apply prod_eq with s1 s2; auto.
    apply H5.
     split.
      assumption.
      split with s1.
       split; apply ref; assumption.
     split with s1.
       assumption.
(* lambda_eq *)
  intros.
    assert (ctxt_eq (S n) (Gamma, A) (Delta, A)).
      split.
       assumption.
       split with s1.
         split; apply ref; auto.
    assert (Delta |-- A ; srt s1).
      auto.
    assert (exists s, Delta |-- A ; srt s).
      split with s1.
      assumption.
    apply lambda_eq with s1 s2 s3; auto.
(* app_eq *)      
  intros.
    apply app_eq with A; auto.
(* ref *)
  intros.
    apply ref.
    auto.
(* sym *)
  intros.
    apply sym.
    auto.
(* trans *)
  intros.
    apply trans with N; auto.
(* conv_eq *)
  intros.
    apply conv_eq with A s; auto.
(* beta *)
  intros.
    assert (Delta |-- A ; srt s1).
      auto.
    assert (ctxt_eq (S n) (Gamma, A) (Delta, A)).
      split.
       assumption.
       split with s1.
         split; apply ref; assumption.
    assert (valid' (n:=S n) (Delta, A)).
      split with s1.
      assumption.
    apply beta with s1 s2 s3; auto.
Qed.

Theorem pre_PTS'_Context_Conversion : forall n (Gamma Delta : context n) M A,
  Gamma |-- M ; A -> Gamma ==c Delta -> valid' Delta -> Delta |-- M ; A.
Proof.
  elim pre_Context_Conversion.
  intros.
  apply H with Gamma; assumption.
Qed.

Theorem pre_PTSeq_Context_Conversion : forall n (Gamma Delta : context n) M N A,
  Gamma |-- M == N ; A -> Gamma ==c Delta -> valid' Delta -> Delta |-- M == N ; A.
Proof.
  elim pre_Context_Conversion.
  intros.
  apply H0 with Gamma; assumption.
Qed.

Theorem Start_Ax : forall n (Gamma : context n) s t,
  axiom s t -> valid' Gamma -> Gamma |-- srt s ; srt t.
Proof.
  induction n; simpl; destruct Gamma.
   intros s t axst _.
     apply ax.
     assumption.
   rename c into Gamma.
     rename t into A.
     destruct 2.
     rename x into t'.
     apply weak with (M := srt (n:=n) s) (A := srt (n:=n) t) (s := t').
      apply IHn; auto.
        apply PTS'_Context_Validity with A (srt (n:=n) t').
        assumption.
      assumption.
Qed.      

Theorem Start_Var : forall (n : nat) (Gamma : context n) (x : fin n),
  valid' Gamma -> Gamma |-- x ; typeof x Gamma.
Proof.
  induction n; simpl.
   destruct x.
   destruct Gamma.
     rename c into Gamma.
     rename t into A.
     destruct x.
     rename f into x.
       destruct 1.
       rename x0 into s.
       apply weak with (M := Terms.var x) (A := typeof x Gamma) (s := s).
        apply IHn; auto.
          apply PTS'_Context_Validity with A (srt (n:=n) s).
          assumption.
        assumption.
     destruct 1.
       rename x into s.
       apply var with (n:=n) (s:=s).
       assumption.
Qed.

Definition satisfy' m n (Gamma : context n) (Delta : context m) (sigma : fin m -> term n) :=
  forall x : fin m, Gamma |-- sigma x ; subst (typeof x Delta) sigma.
Notation "Gamma |== sigma ; Delta" := (satisfy' _ _ Gamma Delta sigma) (at level 70).

Lemma Weak_satisfy'l : forall m n Delta Gamma (sigma : fin m -> term n) A s,
  Gamma |== sigma ; Delta -> Gamma |-- A ; srt s -> ((Gamma, A) : context (S n)) |== up (n:=n) (OO) sigma ; Delta.
Proof.
  unfold satisfy' at 2.
  unfold Comp at 1.
  intros.
  rewrite <- liftterm_subst.
  apply weak with (M := sigma x) (s := s); auto.
Qed.

Lemma Triv_satisfy' : forall n (Gamma : context n), valid' Gamma -> Gamma |== id _ ; Gamma.
Proof.
  unfold satisfy'.
  intros.
  rewrite triv_subst.
  apply Start_Var.
  assumption.
Qed.

Lemma Strength_satisfy' : forall m n Delta Gamma (sigma : fin (S m) -> term n) A,
  Gamma |== sigma ; ((Delta, A) : context (S m)) -> Gamma |== sigma (O) up (n:=m) ; Delta.
Proof.
  unfold satisfy' at 2.
  intros.
  rewrite <- subst_liftterm.
  apply H with (x := up x).
Qed.

Lemma satisfy'_botsub : forall n (Gamma : context n) M A, Gamma |-- M ; A -> Gamma |== botsub M ; ((Gamma, A) : context (S n)).
Proof.
  unfold satisfy'.
  destruct x; simpl; rewrite subst_liftterm; unfold comp; simpl; rewrite triv_subst.
   apply Start_Var.
     apply PTS'_Context_Validity with M A.
     assumption.
   assumption.
Qed.

Theorem Substitution :
  (forall n Gamma M A, Gamma |-- M ; A ->
    forall m Delta (rho : fin n -> term m), Delta |== rho ; Gamma -> valid' Delta -> Delta |-- subst M rho ; subst A rho) /\
  (forall n Gamma M N A, Gamma |-- M == N ; A ->
    forall m Delta (rho : fin n -> term m), Delta |== rho ; Gamma -> valid' Delta -> Delta |-- subst M rho == subst N rho ; subst A rho).
Proof.
  apply PTSeq_induction with
   (P := fun n Gamma M A =>
     forall m Delta (rho : fin n -> term m), Delta |== rho ; Gamma -> valid' Delta -> Delta |-- subst M rho ; subst A rho)
   (P0 := fun n Gamma M N A =>
    forall m Delta (rho : fin n -> term m), Delta |== rho ; Gamma -> valid' Delta -> Delta |-- subst M rho == subst N rho ; subst A rho);
  simpl; intros.
(* ax *)
   apply Start_Ax; assumption.
(* var *)
   apply H1 with (x := bot (n:=n)).
(* weak *)
   repeat rewrite subst_liftterm.
     apply H0.
      apply Strength_satisfy' with B.
        assumption.
      assumption.
(* prod *)
   apply prod with s1 s2; auto.
     apply H3.
      unfold satisfy'.
        destruct x; simpl; rewrite <- liftterm_subst'.
         apply weak with s1; auto.
         apply var with s1; auto.
      split with s1.
        auto.
(* lambda *)
   assert (satisfy' (S n) (S m) (Delta, subst A rho) (Gamma, A) (liftsub rho)).
     unfold satisfy'.
     destruct x; simpl; rewrite <- liftterm_subst'; [apply weak with s1 | apply var with s1]; auto.
   assert (valid' (n:=S m) (Delta, subst A rho)).
     split with s1; auto.
   apply lambda with s1 s2 s3; auto.
(* appl *)
   rewrite subst_subbot.
     apply appl with (subst A rho); auto.
(* conv *)
   apply conv with (subst A rho) s; auto.
(* weak_eq *)
   repeat rewrite subst_liftterm.
     apply H0.
      apply Strength_satisfy' with B.
        assumption.
      assumption.
(* prod_eq *)
   apply prod_eq with s1 s2; auto.
     apply H5.
      unfold satisfy'.
        destruct x; simpl; rewrite <- liftterm_subst'; [apply weak with s1 | apply var with s1]; auto.
      split with s1; auto.
(* lambda_eq *)
   assert (satisfy' (S n) (S m) (Delta, subst A rho) (Gamma, A) (liftsub rho)).
     unfold satisfy'.
     destruct x; simpl; rewrite <- liftterm_subst'; [apply weak with s1 | apply var with s1]; auto.
   assert (valid' (n:=S m) (Delta, subst A rho)).
     split with s1; auto.
   apply lambda_eq with s1 s2 s3; auto.
(* app_eq *)
   rewrite subst_subbot.
     apply app_eq with (subst A rho); auto.
(* ref *)
   apply ref.
     auto.
(* sym *)
   apply sym.
     auto.
(* trans *)
   apply trans with (subst N rho); auto.
(* conv_eq *)
   apply conv_eq with (subst A rho) s; auto.
(* beta *)
   repeat rewrite subst_subbot.
     assert (satisfy' (S n) (S m) (Delta, subst A rho) (Gamma, A) (liftsub rho)).
       unfold satisfy'.
       destruct x; simpl; rewrite <- liftterm_subst'; [apply weak with s1 | apply var with s1]; auto.
     assert (valid' (n:=S m) (Delta, subst A rho)).
       split with s1; auto.
     apply beta with s1 s2 s3; auto.
Qed.

Theorem PTS'_Substitution : forall m n Gamma M A Delta (rho : fin n -> term m),
  Gamma |-- M ; A -> Delta |== rho ; Gamma -> valid' Delta -> Delta |-- subst M rho ; subst A rho.
Proof.
  intros.
  elim Substitution.
  intros.
  apply H2 with Gamma; assumption.
Qed.

Theorem PTS'_Substitution_bot : forall n Gamma A N M B,
  ((Gamma, A) : context (S n)) |-- M ; B -> Gamma |-- N ; A -> Gamma |-- subbot M N ; subbot B N.
Proof.
  intros.
  unfold subbot.
  apply PTS'_Substitution with (Gamma, A).
   assumption.
   apply satisfy'_botsub.
     assumption.
   apply PTS'_Context_Validity with N A.
     assumption.
Qed.

Theorem PTSeq_Substitution : forall m n Gamma M N A Delta (rho : fin n -> term m),
  Gamma |-- M == N ; A -> Delta |== rho ; Gamma -> valid' Delta -> Delta |-- subst M rho == subst N rho ; subst A rho.
Proof.
  elim Substitution.
  intros.
  apply H0 with Gamma; assumption.
Qed.

Theorem Weak_satisfy' : forall m n Gamma Delta (rho : fin n -> term m) A s,
  Gamma |-- A ; srt s -> Delta |== rho ; Gamma -> valid' Delta -> satisfy' (S n) (S m) (Delta, subst A rho) (Gamma, A) (liftsub rho).
Proof.
unfold satisfy' at 2.
intros.
assert (Delta |-- subst A rho ; srt s).
  apply PTS'_Substitution with (Gamma := Gamma) (A := srt (n:=n) s) (rho := rho); assumption.
destruct x; simpl; rewrite <- liftterm_subst'.
 apply weak with s; auto.
 apply var with s.
   assumption.
Qed.

Lemma subctxt_satisfy : forall m n Gamma Delta (rho : fin m -> fin n),
  subctxt Gamma Delta rho -> valid' Gamma -> valid' Delta -> Delta |== Terms.var (n:=n) (O) rho ; Gamma.
Proof.
unfold satisfy'.
intros.
rewrite subst_is_subvar.
rewrite <- H with x.
unfold comp.
apply Start_Var.
assumption.
Qed.

Theorem PTS'_Weakening : forall m n Gamma Delta M A (rho : fin m -> fin n),
  Gamma |-- M ; A -> subctxt Gamma Delta rho -> valid' Delta -> Delta |-- subvar M rho ; subvar A rho.
Proof.
intros.
repeat rewrite <- subst_is_subvar.
apply PTS'_Substitution with Gamma; auto.
apply subctxt_satisfy; auto.
apply PTS'_Context_Validity with M A; assumption.
Qed.

Theorem valid'_Weakening1 : forall n (Gamma : context n) A B s, valid' (n:=S n) (Gamma, A) -> Gamma |-- B ; srt s ->
valid' (n:=S (S n)) (Gamma, B, liftterm A).
Proof.
destruct 1.
split with x.
apply weak with (A := srt (n:=n) x) (s := s); assumption.
Qed.

Theorem PTS'_Weakening1 : forall n (Gamma : context n) A B M C t,
  ((Gamma,A) : context (S n)) |--  M ; C -> Gamma |-- B ; srt t ->
  ((Gamma, B, liftterm A) : context (S (S n))) |-- subvar M (Sfun (up (n:=n))) ; subvar C (Sfun (up (n:=n))).
Proof.
intros.
apply PTS'_Weakening with (Gamma, A).
 assumption.
 unfold subctxt.
   destruct x; simpl; rewrite liftterm_liftterm; rewrite subvar_liftterm; reflexivity.
 apply valid'_Weakening1 with t.
  apply PTS'_Context_Validity with M C.
    assumption.
  assumption.
Qed.

Definition satisfy_eq m n Gamma Delta (rho sigma : fin m -> term n) :=
  forall x, Gamma |-- rho x == sigma x ; subst (typeof x Delta) rho.
Notation "Gamma |== rho == sigma ; Delta" := (satisfy_eq _ _ Gamma Delta rho sigma) (at level 70).

Lemma Weak_satisfy_eql : forall n Gamma m Delta (rho sigma : fin n -> term m) A s,
  Delta |== rho == sigma ; Gamma -> Delta |-- A ; srt s ->
    ((Delta, A) : context (S m)) |== up (n:=m) (OO) rho == up (n:=m) (OO) sigma ; Gamma.
Proof.
unfold satisfy_eq at 2.
intros.
rewrite <- liftterm_subst.
unfold Comp.
apply weak_eq with (M := rho x) (N := sigma x) (s := s); auto.
Qed.

Lemma pre_Weak_satisfy_eq : forall m n Gamma Delta (rho sigma : fin n -> term m) A s,
  Delta |== rho ; Gamma -> Delta |== rho == sigma ; Gamma -> Gamma |-- A ; srt s -> valid' Delta ->
  satisfy_eq (S n) (S m) (Delta, subst A rho) (Gamma, A) (liftsub rho) (liftsub sigma).
Proof.
unfold satisfy_eq at 2.
destruct x; simpl.
 rewrite <- liftterm_subst'.
   apply weak_eq with s.
    apply H0.
    apply PTS'_Substitution with (A := srt (n:=n) s) (rho := rho) (Gamma := Gamma); assumption.
 apply ref.
   rewrite <- liftterm_subst'.
   apply var with s.
   apply PTS'_Substitution with (A := srt (n:=n) s) (rho := rho) (Gamma := Gamma); assumption.
Qed.

Lemma satisfy_eq_ref : forall n Gamma m Delta (rho : fin n -> term m),
  Delta |== rho ; Gamma -> Delta |== rho == rho ; Gamma.
Proof.
unfold satisfy_eq.
intros.
apply ref.
auto.
Qed.

Lemma Strength_satisfy_eq : forall m n Gamma Delta A (sigma rho : fin (S m) -> term n),
  Delta |== rho == sigma ; ((Gamma, A) : context (S m)) -> Delta |== rho (O) up (n:=m) == sigma (O) up (n:=m) ; Gamma.
Proof.
unfold satisfy_eq.
intros.
rewrite <- subst_subvar.
unfold comp.
apply H with (x := up x).
Qed.

Theorem pre_Functionality : forall n Gamma M A, Gamma |-- M ; A ->
  forall m Delta (rho sigma : fin n -> term m),
  Delta |== rho == sigma ; Gamma -> Delta |== rho ; Gamma -> valid' Delta ->
    Delta |-- subst M rho == subst M sigma ; subst A rho.
Proof.
induction 1; simpl.
(* ax *)
 intros.
   apply ref.
   apply Start_Ax; assumption.
(* var *)
 intros.
   change (liftterm A) with (typeof (n:=S n) bot (Gamma, A)).
   apply H0.
(* weak *)
 intros.
   repeat rewrite subst_liftterm.
   apply IHPTS'1.
    apply Strength_satisfy_eq with B.
      assumption.
    apply Strength_satisfy' with B.
      assumption.
    assumption.
(* prod *)
 intros.
   assert (Delta |-- subst A rho ; srt s1).
     apply PTS'_Substitution with (A := srt (n:=n) s1) (rho := rho) (Gamma := Gamma); assumption.    
   apply prod_eq with s1 s2; auto.
    apply IHPTS'1 with (rho := rho); assumption.
    apply IHPTS'2 with (rho := liftsub rho).
     apply pre_Weak_satisfy_eq with s1; assumption.
     apply Weak_satisfy' with s1; assumption.
     split with s1.
       assumption.
(* lambda *)
 intros.
   assert (Delta |-- subst A rho ; srt s1).
     apply PTS'_Substitution with (rho := rho) (A := srt (n:=n) s1) (Gamma := Gamma); assumption.
   apply lambda_eq with s1 s2 s3; auto.
    apply IHPTS'2.
      apply pre_Weak_satisfy_eq with s1; assumption.
      apply Weak_satisfy' with s1; assumption.
      split with s1.
        assumption.
    apply IHPTS'1 with (rho := rho); assumption.
    apply PTS'_Substitution with (rho := liftsub rho) (A := srt (n:=S n) s2) (Gamma := (Gamma, A)).
     assumption.
     apply Weak_satisfy' with s1; assumption.
     split with s1.
       assumption.
(* appl *)
 intros.
   rewrite subst_subbot.
   apply app_eq with (subst A rho).
    apply IHPTS'1 with (rho := rho); assumption.
    apply IHPTS'2 with (rho := rho); assumption.
(* conv *)
 intros.
   apply conv_eq with (subst A rho) s.
   apply IHPTS'; assumption.
   apply PTSeq_Substitution with (A := srt (n:=n) s) (rho := rho) (Gamma := Gamma); assumption.
Qed.

Theorem pre_Functionality_bot : forall n Gamma A M B N N', ((Gamma, A) : context (S n)) |-- M ; B ->
  Gamma |-- N == N' ; A -> Gamma |-- N ; A -> Gamma |-- subbot M N == subbot M N' ; subbot B N.
Proof.
intros.
unfold subbot.
assert (valid' Gamma).
  apply PTS'_Context_Validity with N A.
  assumption.
assert (forall f : fin n, Gamma |-- f ; subbot (liftterm (typeof f Gamma)) N).
  intro.
  rewrite subbot_liftterm.
  apply Start_Var.
  assumption.
apply pre_Functionality with (Gamma, A); auto; intro x; destruct x; simpl.
 apply ref.
   exact (H3 f).
 change (subst (liftterm A) (botsub N)) with (subbot (liftterm A) N).
   rewrite subbot_liftterm.
   assumption.
 exact (H3 f).
 change (subst (liftterm A) (botsub N)) with (subbot (liftterm A) N).
   rewrite subbot_liftterm.
   assumption.
Qed.

(* Equivalence of Terms *)

Inductive equiv (n : nat) (Gamma : context n) : term n -> term n -> Prop :=
  equiv_ref : forall (M : term n), equiv _ Gamma M M |
  equiv_cons : forall (M N P A : term n), equiv _ Gamma M N -> Gamma |-- N == P ; A -> equiv _ Gamma M P.

Notation "Gamma |= M =* N" := (equiv _ Gamma M N) (at level 70).

Hint Resolve equiv_ref.

Lemma equiv_consl : forall n (Gamma : context n) N P, Gamma |= N =* P -> forall M A, Gamma |-- M == N ; A ->
  Gamma |= M =* P.
Proof.
induction 1.
 intros.
   apply equiv_cons with M0 A; auto.
 intros.
   apply equiv_cons with N A.
    apply IHequiv with A0.
      assumption.
    assumption.
Qed.

Lemma equiv_sym : forall n (Gamma : context n) M N, Gamma |= M =* N -> Gamma |= N =* M.
Proof.
induction 1.
 apply equiv_ref.
 apply equiv_consl with N A.
  assumption.
  apply sym.
    assumption.
Qed.

Lemma equiv_trans : forall n (Gamma : context n) M N, Gamma |= M =* N -> forall P, Gamma |= N =* P -> Gamma |= M =* P.
Proof.
induction 1.
 auto.
 intros.
   apply IHequiv.
   apply equiv_consl with P A; assumption.
Qed.

Lemma equiv_weak : forall n (Gamma : context n) M N, Gamma |= M =* N ->
  forall A s, Gamma |-- A ; srt s -> ((Gamma, A) : context (S n)) |= liftterm M =* liftterm N.
Proof.
induction 1.
 intros.
   apply equiv_ref.
 intros.
   apply equiv_cons with (liftterm N) (liftterm A).
    apply IHequiv with s.
      assumption.
    apply weak_eq with s; assumption.
Qed.
    
(* Generation Lemma *)

Lemma pre_Gen_sort : forall n (Gamma : context n) M A, Gamma |-- M ; A -> forall s, M = srt s ->
  exists t, axiom s t /\ Gamma |= A =* srt t.
Proof.
induction 1; try discriminate 1.
 injection 1.
   clear H0.
   destruct 1.
   split with t.
   auto.
 intros.
   elim IHPTS'1 with s0.
    destruct 1.
      rename x into t.
      split with t.
      split.
       assumption.
       apply equiv_weak with (N := srt (n:=n) t) (s := s); assumption.
    apply liftterm_srt.
      assumption.
 intros.
   elim IHPTS' with s0.
    destruct 1.
      rename x into t.
      split with t.
      split.
       assumption.
       apply equiv_consl with A (srt (n:=n) s).
        assumption.
        apply sym.
          assumption.
    assumption.
Qed.

Lemma Gen_sort : forall n (Gamma : context n) s A, Gamma |-- srt s ; A ->
  exists t, axiom s t /\ Gamma |= A =* srt t.
Proof.
intros.
apply pre_Gen_sort with (srt (n:=n) s); auto.
Qed.

Lemma pre_Gen_var : forall n (Gamma : context n) M A, Gamma |-- M ; A ->
  forall x : fin n, M = x ->
  Gamma |= A =* typeof x Gamma.
Proof.
induction 1; try discriminate 1; intros.
 replace x with (bot (n:=n)).
  auto.
  apply var_inj.
    assumption.
 elim liftterm_var with n M x.
  destruct 1.
    rename x0 into y.
    rewrite H3.
    simpl.
    apply equiv_weak with s.
     apply IHPTS'1.
       assumption.
     assumption.
  assumption.
 apply equiv_consl with A (srt (n:=n) s).
  apply IHPTS'.
    assumption.
  apply sym.
    assumption.
Qed.

Lemma Gen_var : forall n Gamma (x : fin n) A,
  Gamma |-- x ; A -> Gamma |= A =* typeof x Gamma.
Proof.
intros.
apply pre_Gen_var with (Terms.var x); auto.
Qed.

Lemma pre_Gen_product : forall n (Gamma : context n) M C, Gamma |-- M ; C ->
  forall A B, M = pi A B ->
  exists s1, exists s2, exists s3, rule s1 s2 s3 /\
  Gamma |-- A ; srt s1 /\ ((Gamma, A) : context (S n)) |-- B ; srt s2 /\ Gamma |= C =* srt s3.
Proof.
induction 1; try discriminate 1; intros.
(* weak *)
 elim liftterm_pi with n M A0 B0.
  clear H1.
    intro A'.
    destruct 1.
    rename x into B'.
    destruct H1.
    rewrite H1 in H.
    rewrite H1 in IHPTS'1.
    clear M H1.
    destruct H2.
    rewrite <- H1.
    clear A0 H1.
    rewrite <- H2.
    clear B0 H2.
    elim IHPTS'1 with A' B'; auto.
    clear IHPTS'1.
    intro s1.
    destruct 1.
    rename x into s2.
    destruct H1.
    rename x into s3.
    destruct H1.
    destruct H2.
    destruct H3.
    split with s1.
    split with s2.
    split with s3.
    split.
     assumption.
    split.
     apply weak with (A := srt (n:=n) s1) (s := s); assumption.
    split.
     apply PTS'_Weakening with (A := srt (n := S n) s2) (rho := Sfun (up (n:=n))) (Gamma := (Gamma, A')).
      assumption.
      unfold subctxt.
        destruct x; simpl; rewrite liftterm_liftterm; rewrite subvar_liftterm; apply subvar_ext; unfold funceq; reflexivity.
      apply valid'_Weakening1 with (n := n) (s := s).
       split with s1.
	 assumption.
       assumption.
     apply equiv_weak with (N := srt (n:=n) s3) (s := s); assumption.
  assumption.
(* prod *)
 split with s1.
   split with s2.
   split with s3.
   split.
    assumption.
    rewrite <- pi_injl with n A A0 B B0.
     rewrite <- pi_injr with n A A0 B B0; auto.
     assumption.
(* conv *)
 elim IHPTS' with A0 B0.
  intro s1.
    destruct 1.
    rename x into s2.
    destruct H2.
    rename x into s3.
    destruct H2.
    destruct H3.
    destruct H4.
    split with s1.
    split with s2.
    split with s3.
    split.
     assumption.
    split.
     assumption.
    split.
     assumption.
     apply equiv_consl with A (srt (n:=n) s).
      assumption.
      apply sym.
        assumption.
  assumption.
Qed.

Theorem Gen_product : forall n (Gamma : context n) A B C, Gamma |-- pi A B ; C ->
  exists s1, exists s2, exists s3, rule s1 s2 s3 /\
  Gamma |-- A ; srt s1 /\ ((Gamma, A) : context (S n)) |-- B ; srt s2 /\ Gamma |= C =* srt s3.
Proof.
intros.
apply pre_Gen_product with (pi A B); auto.
Qed.

Lemma pre_Gen_abs : forall n (Gamma : context n) N B, Gamma |-- N ; B ->
  forall A M, N = lda A M ->
  exists s1, exists s2, exists s3, exists C,
  rule s1 s2 s3 /\ Gamma |-- A ; srt s1 /\ ((Gamma, A) : context (S n)) |-- C ; srt s2 /\ ((Gamma, A) : context (S n)) |-- M ; C 
    /\ Gamma |= B =* pi A C.
Proof.
induction 1; try discriminate 1.
(* weak *)
 clear IHPTS'2.
   intros.
   elim liftterm_lda with n M A0 M0.
    clear H1.
      intro A'.
      destruct 1.
      rename x into M'.
      destruct H1.
      destruct H2.
      rewrite <- H2.
      clear A0 H2.
      rewrite <- H3.
      clear M0 H3.
      elim IHPTS'1 with A' M'.
       intro s1.
         destruct 1.
	 rename x into s2.
	 destruct H2.
	 rename x into s3.
	 destruct H2.
	 rename x into C.
	 destruct H2.
	 destruct H3.
	 destruct H4.
	 destruct H5.
	 split with s1.
	 split with s2.
	 split with s3.
	 split with (subvar C (Sfun (up (n:=n)))).
	 split.
	  assumption.
	 split.
	  apply weak with (A := srt (n:=n) s1) (s := s); assumption.
	 split.
	  apply PTS'_Weakening1 with (C := srt (n:=S n) s2) (t := s); assumption.
	 split.
	  apply PTS'_Weakening1 with (C := C) (t := s); assumption.
	  change (pi (liftterm A') (subvar C (Sfun (up (n:=n))))) with (liftterm (pi A' C)).
	    apply equiv_weak with s; assumption.
       assumption.
    assumption.
(* lambda *)
 clear IHPTS'1 IHPTS'2 IHPTS'3.
   intros.
   rewrite <- lda_injl with n A A0 M M0.
    rewrite <- lda_injr with n A A0 M M0.
     clear A0 M0 H3.
       split with s1.
       split with s2.
       split with s3.
       split with B.
       auto.
     assumption.
    assumption.
(* conv *)
 intros.
   elim IHPTS' with A0 M0.
    intro s1.
      destruct 1.
      rename x into s2.
      destruct H2.
      rename x into s3.
      destruct H2.
      rename x into C.
      destruct H2.
      destruct H3.
      destruct H4.
      destruct H5.
      split with s1.
      split with s2.
      split with s3.
      split with C.
      split.
       assumption.
      split.
       assumption.
      split.
       assumption.
      split.
       assumption.
       apply equiv_consl with A (srt (n:=n) s).
        assumption.
	apply sym.
	  assumption.
  assumption.
Qed.

Theorem Gen_abs : forall n (Gamma : context n) A M B, Gamma |-- lda A M ; B ->
  exists s1, exists s2, exists s3, exists C,
    rule s1 s2 s3 /\ Gamma |-- A ; srt s1 /\ ((Gamma, A) : context (S n)) |-- C ; srt s2 /\ ((Gamma, A) : context (S n)) |-- M ; C 
      /\ Gamma |= B =* pi A C.
Proof.
intros.
apply pre_Gen_abs with (lda A M); auto.
Qed.

Theorem pre_Gen_app : forall n (Gamma : context n) P C, Gamma |-- P ; C ->
  forall M N, P = app M N ->
    exists A, exists B, Gamma |-- M ; pi A B /\ Gamma |-- N ; A /\ Gamma |= subbot B N =* C.
Proof.
induction 1; try discriminate 1.
(* weak *)
 clear IHPTS'2.
   intros.
   elim liftterm_app with n M M0 N.
    clear H1.
      intro M'.
      destruct 1.
      rename x into N'.
      destruct H1.
      destruct H2.
      rewrite <- H2.
      clear M0 H2.
      rewrite <- H3.
      clear N H3.
      elim IHPTS'1 with M' N'.
       clear H1.
         intro A0.
	 destruct 1.
	 rename x into B0.
	 destruct H1.
	 destruct H2.
	 split with (liftterm A0).
	 split with (subvar B0 (Sfun (up (n:=n)))).
	 split.
	  apply weak with (A := (pi A0 B0)) (s := s); assumption.
	 split.
	  apply weak with s; assumption.
	  rewrite <- liftterm_subbot.
            apply equiv_weak with s; assumption.
       assumption.
    assumption.
(* appl *)
 clear IHPTS'1 IHPTS'2.
   intros.
   rewrite <- app_injl with n M M0 N N0.
    rewrite <- app_injr with n M M0 N N0.
     split with A.
       split with B.
       auto.
     assumption.
    assumption.
(* conv *)
 intros.
   elim IHPTS' with M0 N.
    intro A0.
      destruct 1.
      rename x into B0.
      destruct H2.
      destruct H3.
      split with A0.
      split with B0.
      split.
       assumption.
      split.
       assumption.
       apply equiv_cons with A (srt (n:=n) s); assumption.
    assumption.
Qed.

Theorem Gen_app : forall n (Gamma : context n) M N C, Gamma |-- app M N ; C ->
  exists A, exists B,
    Gamma |-- M ; pi A B /\ Gamma |-- N ; A /\ Gamma |= subbot B N =* C.
Proof.
intros.
apply pre_Gen_app with (app M N); auto.
Qed.

Theorem Type_Eq_Valid : (forall n (Gamma : context n) M A, Gamma |-- M ; A -> (exists s, A = srt s) \/ exists s, Gamma |-- A ; srt s) /\
  (forall n (Gamma : context n) M N A, Gamma |-- M == N ; A -> Gamma |-- M ; A /\ Gamma |-- N ; A /\
    ((exists s, A = srt s) \/ exists s, Gamma |-- A ; srt s)).
Proof.
apply PTSeq_induction with
  (P := fun n (Gamma : context n) (M A : term n) => (exists s, A = srt s) \/ exists s, Gamma |-- A ; srt s)
  (P0 := fun n (Gamma : context n) M N A => Gamma |-- M ; A /\ Gamma |-- N ; A /\ ((exists s, A = srt s) \/ exists s, Gamma |-- A ; srt s)).
(* ax *)
 left.
   split with t.
   reflexivity.
(* var *)
 right.
   split with s.
   apply weak with (A := srt (n:=n) s) (s := s); assumption.
(* weak *)
 destruct 2; destruct H0; rename x into t.
  left.
    split with t.
    rewrite H0.
    reflexivity.
  right.
    split with t.
    apply weak with (A := srt (n:=n) t) (s:=s); assumption.
(* prod *)
 left.
   split with s3.
   reflexivity.
(* lambda *)
 right.
   split with s3.
   apply prod with s1 s2; assumption.
(* appl *)
 destruct 2; destruct H0.
  discriminate H0.
  rename x into s3.
    elim Gen_product with n Gamma A B (srt (n:=n) s3).
     intro s1.
       destruct 1.
       rename x into s2.
       destruct H1.
       rename x into s3'.
       destruct H1.
       destruct H2.
       destruct H3.
       right.
       split with s2.
       apply PTS'_Substitution_bot with (B := srt (n:=S n) s2) (N := N) (A := A); assumption.
     assumption.
(* conv *)
 right.
   split with s.
   destruct H2.
   destruct H3.
   assumption.
(* weak_eq *)
 destruct 2.
   destruct H1.
   split.
    apply weak with s; assumption.
   split.
    apply weak with s; assumption.
    destruct H2.
     left.
       destruct H2.
       rename x into t.
       split with t.
       rewrite H2.
       reflexivity.
     right.
       destruct H2.
       rename x into t.
       split with t.
       apply weak with (A := srt (n:=n) t) (s := s); assumption.
(* prod_eq *)
 destruct 3.
   destruct H2.
   destruct 4.
   destruct H8.
   split.
    apply prod with s1 s2; assumption.
   split.
    apply prod with s1 s2; auto.
      apply pre_PTS'_Context_Conversion with (Gamma, A).
       assumption.
       split.
        apply ctxt_eq_ref.
          apply PTS'_Context_Validity with A (srt (n:=n) s1).
	  assumption.
        split with s1.
	  auto.
       split with s1.
         assumption.
    left.
      split with s3.
      reflexivity.
(* lambda_eq *)
 destruct 3.
   destruct H2.
   destruct 2.
   destruct H6.
   assert (valid' Gamma).
     apply PTS'_Context_Validity with A (srt (n:=n) s1).
     assumption.
   assert (ctxt_eq (S n) (Gamma, A) (Gamma, A')).
     split.
      apply ctxt_eq_ref.
        assumption.
      split with s1.
        split; assumption.
   assert (valid' (n:=S n) (Gamma, A')).
     split with s1.
     assumption.
   split.
    apply lambda with s1 s2 s3; assumption.
   split.
    apply conv with (pi A' B) s3.
     apply lambda with s1 s2 s3; try assumption; apply pre_PTS'_Context_Conversion with (Gamma, A); assumption.
     apply prod_eq with s1 s2; try assumption.
      apply sym.
        assumption.
      apply ref.
        apply pre_PTS'_Context_Conversion with (Gamma, A); assumption.
    right.
      split with s3.
      apply prod with s1 s2; assumption.
(* app_eq *)
 destruct 2.
   destruct H1.
   destruct 2.
   destruct H5.
   split.
    apply appl with A; assumption.
    destruct H2; destruct H2.
     discriminate H2.
     rename x into s3.
       elim Gen_product with n Gamma A B (srt (n:=n) s3).
        intro s1.
	  destruct 1.
	  rename x into s2.
	  destruct H7.
	  rename x into s3'.
	  destruct H7.
	  destruct H8.
	  destruct H9.
	  split.
	   apply conv with (subbot B N') s2.
	    apply appl with A; assumption.
	    apply sym.
	      apply pre_Functionality_bot with (B := srt (n:=S n) s2) (N := N) (A := A); auto.
           right.
	     split with s2.
	     apply PTS'_Substitution_bot with (B := srt (n:=S n) s2) (N := N) (A := A); auto.
        assumption.
(* ref *)
 auto.
(* sym *)
 tauto.
(* trans *)
 tauto.
(* conv_eq *)
 destruct 2.
   destruct H1.
   destruct 2.
   destruct H5.
   split.
    apply conv with A s; assumption.
   split.
    apply conv with A s; assumption.
    right.
      split with s.
      assumption.
(* beta *)
 fold context.
   split.
    apply appl with A.
      apply lambda with s1 s2 s3; assumption.
      assumption.
   split.
    apply PTS'_Substitution_bot with A; assumption.
    right.
      split with s2.
      apply PTS'_Substitution_bot with (A := A) (B := srt (n:=S n) s2) (N := M); assumption.
Qed.

Theorem PTS'_Type_Validity : forall n (Gamma : context n) M A, Gamma |-- M ; A -> (exists s, A = srt s) \/ exists s, Gamma |-- A ; srt s.
Proof.
elim Type_Eq_Valid.
trivial.
Qed.

Theorem PTSeq_Type_Validity : forall n (Gamma : context n) M N A, Gamma |-- M == N ; A -> (exists s, A = srt s) \/ exists s, Gamma |-- A ; srt s.
Proof.
elim Type_Eq_Valid.
intros.
elim H0 with n Gamma M N A.
 tauto.
 assumption.
Qed.

Theorem Equation_Validity_l : forall n (Gamma : context n) M N A, Gamma |-- M == N ; A -> Gamma |-- M ; A.
Proof.
elim Type_Eq_Valid.
intros.
elim H0 with n Gamma M N A; auto.
Qed.

Theorem Equation_Validity_r : forall n (Gamma : context n) M N A, Gamma |-- M == N ; A -> Gamma |-- N ; A.
Proof.
elim Type_Eq_Valid.
intros.
elim H0 with n Gamma M N A.
 tauto.
 assumption.
Qed.

Lemma ctxt_eq_validl : forall n (Gamma Delta : context n), Gamma ==c Delta -> valid' Gamma.
Proof.
induction n; simpl.
 auto.
 destruct Gamma.
   rename c into Gamma.
   rename t into A.
   destruct Delta.
   rename c into Delta.
   rename t into B.
   destruct 1.
   destruct H0.
   rename x into s.
   destruct H0.
   split with s.
   apply Equation_Validity_l with B.
   assumption.
Qed.

Lemma ctxt_eq_validr : forall n (Gamma Delta : context n), Gamma ==c Delta -> valid' Delta.
Proof.
induction n; simpl.
 auto.
 destruct Gamma.
   rename c into Gamma.
   rename t into A.
   destruct Delta.
   rename c into Delta.
   rename t into B.
   destruct 1.
   destruct H0.
   rename x into s.
   destruct H0.
   split with s.
   apply Equation_Validity_r with A.
   assumption.
Qed.

Theorem PTS'_Context_Conversion : forall n (Gamma Delta : context n) M A, Gamma |-- M ; A -> Gamma ==c Delta -> Delta |-- M ; A.
Proof.
intros.
apply pre_PTS'_Context_Conversion with Gamma; auto.
apply ctxt_eq_validr with Gamma.
assumption.
Qed.

Theorem PTSeq_Context_Conversion : forall n (Gamma Delta : context n) M N A, Gamma |-- M == N ; A -> Gamma ==c Delta -> Delta |-- M == N ; A.
Proof.
intros.
apply pre_PTSeq_Context_Conversion with Gamma; auto.
apply ctxt_eq_validr with Gamma.
assumption.
Qed.

Lemma satisfy_eq_validl : forall m n Gamma Delta (rho sigma : fin m -> term n),
  Gamma |== rho == sigma ; Delta -> Gamma |== rho ; Delta.
Proof.
intros.
intro x.
apply Equation_Validity_l with (sigma x).
apply H.
Qed.

Theorem Functionality : forall m n Gamma Delta M A (rho sigma : fin m -> term n),
  Gamma |-- M ; A -> Delta |== rho == sigma ; Gamma -> valid' Delta -> Delta |-- subst M rho == subst M sigma ; subst A rho.
Proof.
intros.
apply pre_Functionality with Gamma; auto.
apply satisfy_eq_validl with sigma.
assumption.
Qed.

Lemma satisfy_eq_validr : forall m n Gamma Delta (rho sigma : fin m -> term n),
  Gamma |== rho == sigma ; Delta -> valid' Gamma -> valid' Delta -> Gamma |== sigma ; Delta.
Proof.
intros.
intro x.
apply Equation_Validity_r with (rho x).
elim PTS'_Type_Validity with m Delta (Terms.var x) (typeof x Delta).
 destruct 1.
   rename x0 into s.
   rewrite H2.
   change (subst (srt s) sigma) with (subst (srt s) rho).
   rewrite <- H2.
   apply H.
 destruct 1.
   rename x0 into s.
   apply conv_eq with (subst (typeof x Delta) rho) s.
    apply H.
    apply Functionality with (A := srt (n:=m) s) (rho := rho) (Gamma := Delta); assumption.
    apply Start_Var.
      assumption.
Qed.
