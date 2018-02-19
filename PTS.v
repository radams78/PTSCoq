Require Export Conv.
Require Import CR.

(* Contexts *)

Fixpoint context (n : nat) {struct n} : Set :=
  match n with
  | O => unit
  | (S m) => prod (context m) (term m)
  end.

Definition typeof : forall n : nat, fin n -> context n -> term n.
  induction n.
  intro x.
    case x.
  intro x.
    case x.
    intros y Gamma.
      case Gamma. 
      intros Delta A.
      exact (liftterm (IHn y Delta)).
    intro Gamma.
      case Gamma.
      intros Delta A.
      exact (liftterm A).
Defined.
Implicit Arguments typeof [n].

Definition subctxt (m n : nat) (Delta : context m) (Gamma : context n) (rho : fin m -> fin n) :=
  forall (x : fin m), typeof (rho x) Gamma = subvar (typeof x Delta) rho.
Implicit Arguments subctxt [m n].

Lemma subctxt_ext : forall (m n : nat) (Delta : context m) (Gamma : context n) (rho sigma : fin m -> fin n),
  rho =f sigma -> subctxt Delta Gamma rho -> subctxt Delta Gamma sigma.
Proof.
unfold subctxt.
intros.
rewrite <- H with x.
transitivity (subvar (typeof x Delta) rho).
 apply H0.
 apply subvar_ext.
   assumption.
Qed.

Lemma Triv_subctxt : forall (n : nat) (Gamma : context n), subctxt Gamma Gamma (id _).
Proof.
unfold subctxt.
intros.
symmetry.
apply triv_subvar.
Qed.

Lemma Weak_subctxtr : forall (m n : nat) (Delta : context m) (Gamma : context n) (rho : fin m -> fin n) (A : term n),
  subctxt Delta Gamma rho -> subctxt (n:=S n) Delta (Gamma, A) (up (n:=n) (O) rho).
Proof.
unfold subctxt.
intros.
simpl.
rewrite H.
apply liftterm_subvar with (rho := rho).
Qed.

Lemma Weak_subctxt : forall (m n : nat) (Delta : context m) (Gamma : context n) (rho : fin m -> fin n) (A : term m),
  subctxt Delta Gamma rho -> subctxt (m:=S m) (n:=S n) (Delta, A) (Gamma, subvar A rho) (Sfun rho).
Proof.
unfold subctxt at 2.
destruct x; simpl.
 fold fin in f.
   rewrite H with f.
   rewrite subvar_liftterm.
   apply liftterm_subvar with (rho := rho).
 rewrite subvar_liftterm.
   apply liftterm_subvar with (rho := rho).
Qed.

Lemma Strength_subctxt : forall (m n : nat) (Delta : context m) (Gamma : context n) (rho : fin (S m) -> fin n) (A : term m),
  subctxt (m:=S m) (Delta, A) Gamma rho -> subctxt Delta Gamma (rho (O) up (n:=m)).
Proof.
unfold subctxt.
intros.
unfold comp at 1.
rewrite H with (up x).
simpl.
apply subvar_liftterm with (rho := rho).
Qed.

(* Reduction of a Context *)

Definition par_red1_ctxt (n : nat) (Gamma Delta : context n) :=
  forall x, typeof x Gamma |> typeof x Delta.
Implicit Arguments par_red1_ctxt [n].
Notation "Gamma |c> Delta" := (par_red1_ctxt Gamma Delta) (at level 80).

Lemma par_red1_ctxt_ref : forall (n : nat) (Gamma : context n),
  Gamma |c> Gamma.
Proof.
unfold par_red1_ctxt.
auto.
Qed.
Hint Resolve par_red1_ctxt_ref.

Lemma par_red1_ctxt_build : forall n (Gamma Delta : context n) (A B : term n),
  Gamma |c> Delta -> A |> B -> ((Gamma, A) : context (S n)) |c> (Delta, B).
Proof.
unfold par_red1_ctxt.
destruct x; simpl; apply par_red1_liftterm; auto.
Qed.

Lemma par_red1_ctxt_injl : forall n (Gamma Delta : context n) (A B : term n),
  ((Gamma, A) : context (S n)) |c> (Delta, B) -> Gamma |c> Delta.
Proof.
unfold par_red1_ctxt.
intros.
apply par_red1_liftterm_inj.
apply H with (x := up x).
Qed.

Lemma par_red1_ctxt_injr : forall n (Gamma Delta : context n) (A B : term n),
  ((Gamma, A) : context (S n)) |c> (Delta, B) -> A |> B.
Proof.
unfold par_red1_ctxt.
intros.
apply par_red1_liftterm_inj.
apply H with (x := bot (n:=n)).
Qed.
 
(* Convertible Contexts *)

Definition conv_ctxt (n : nat) (Gamma Delta : context n) :=
  forall x, typeof x Gamma ~= typeof x Delta.
Implicit Arguments conv_ctxt [n].
Notation "Gamma ~=c Delta" := (conv_ctxt Gamma Delta) (at level 80).

Lemma conv_ctxt_ref : forall (n : nat) (Gamma : context n), Gamma ~=c Gamma.
Proof.
unfold conv_ctxt.
auto.
Qed.
Hint Resolve conv_ctxt_ref.

Lemma conv_ctxt_build : forall n (Gamma Delta : context n) (A B : term n),
 Gamma ~=c Delta -> A ~= B -> ((Gamma, A) : context (S n)) ~=c (Delta, B).
Proof.
unfold conv_ctxt.
destruct x; simpl; apply conv_liftterm; auto.
Qed.

Lemma conv_ctxt_injl : forall n (Gamma Delta : context n) (A B : term n),
 ((Gamma, A) : context (S n)) ~=c (Delta, B) -> Gamma ~=c Delta.
Proof.
unfold conv_ctxt.
intros.
apply conv_liftterm_inj.
apply H with (x := up x).
Qed.

Lemma conv_ctxt_injr : forall n (Gamma Delta : context n) (A B : term n),
 ((Gamma, A) : context (S n)) ~=c (Delta, B) -> A ~= B.
Proof.
unfold conv_ctxt.
intros.
apply conv_liftterm_inj.
apply H with (x := bot (n:=n)).
Qed.


(* PTS specifications *)

Parameter axiom : sort -> sort -> Prop.
Parameter rule : sort -> sort -> sort -> Prop.

(* Rules of Deduction of a PTS *)

Inductive PTS : forall n : nat, context n -> term n -> term n -> Prop :=
  axioms : forall s t : sort, axiom s t -> PTS O tt (srt s) (srt t) |
  start : forall n : nat, forall Gamma : context n, forall A : term n, forall s : sort,
   PTS _ Gamma A (srt s) -> PTS (S n) (Gamma, A) bot (liftterm A) |
  weakening : forall n : nat, forall Gamma : context n, forall A B C : term n, forall s : sort,
   PTS _ Gamma A B -> PTS _ Gamma C (srt s) -> PTS (S n) (Gamma, C) (liftterm A) (liftterm B) |
  product : forall n : nat, forall Gamma : context n, forall A : term n, forall B : term (S n), forall s1 s2 s3 : sort,
   rule s1 s2 s3 ->
   PTS _ Gamma A (srt s1) -> PTS (S n) (Gamma, A) B (srt s2) -> PTS _ Gamma (pi A B) (srt s3) |
  application : forall n : nat, forall Gamma : context n, forall F A a : term n, forall B : term (S n),
   PTS _ Gamma F (pi A B) -> PTS _ Gamma a A -> PTS _ Gamma (app F a) (subbot B a) |
  abstraction : forall n : nat, forall Gamma : context n, forall A : term n, forall b B : term (S n), forall s1 s2 s3 : sort,
   rule s1 s2 s3 ->
   PTS (S n) (Gamma, A) b B -> PTS _ Gamma A (srt s1) -> PTS (S n) (Gamma, A) B (srt s2) -> PTS _ Gamma (lda A b) (pi A B) |
  conversion : forall n : nat, forall Gamma : context n, forall A B B' : term n, forall s : sort,
   B ~= B' ->
   PTS _ Gamma A B -> PTS _ Gamma B' (srt s) -> PTS _ Gamma A B'.
Implicit Arguments PTS [n].
Notation "Gamma |- M ; A" := (PTS Gamma M A) (at level 80).

Definition valid : forall n : nat, context n -> Prop.
  intro n.
  case n; simpl.
  intro.
    exact True.
  destruct 1.
    exact (exists s : sort, PTS c t (srt s)).
Defined.
Implicit Arguments valid [n].

Lemma Weak_valid : forall (n : nat) (Gamma : context n) (A B : term n) (s : sort),
  valid (n := S n) (Gamma, B) -> Gamma |- A ; srt s -> valid (n := S (S n)) (Gamma, A, liftterm B).
Proof.
simpl.
destruct 1.
rename x into t.
split with t.
apply weakening with (B := srt (n:=n) t) (s:=s); assumption.
Qed.

Theorem Context_Validity : forall (n : nat) (Gamma : context n) (M A : term n),
  Gamma |- M ; A -> valid Gamma.
Proof.
induction 1; auto.
split.
split with s.
  assumption.
split with s.
  assumption.
Qed.

Theorem Start_ax : forall n (Gamma : context n) s t,
  axiom s t -> valid Gamma -> Gamma |- srt s ; srt t.
Proof.
induction n; simpl; destruct Gamma.
 intros.
   apply axioms.
   assumption.
 rename c into Gamma.
   rename t into A.
   destruct 2.
   rename x into s'.
   apply weakening with (A := srt (n:=n) s) (B := srt (n:=n) t) (s := s').
    apply IHn.
     assumption.
     apply Context_Validity with A (srt (n:=n) s').
       assumption.
    assumption.
Qed.

Theorem Start_var : forall n (Gamma : context n) (x : fin n),
  valid Gamma -> Gamma |- x ; typeof x Gamma.
Proof.
induction n; simpl; destruct Gamma; destruct x; rename c into Gamma; rename t into A.
 rename f into x.
   destruct 1.
   rename x0 into s.
   apply weakening with (A := var x) (B := typeof x Gamma) (s := s).
    apply IHn.
      apply Context_Validity with A (srt (n:=n) s).
      assumption.
    assumption.
 destruct 1.
   rename x into s.
   apply start with (Gamma := Gamma) (A := A) (s := s).
   assumption.
Qed.

(* Satisfaction of a context *)

Definition satisfy (m n : nat) (Gamma : context n) (sigma : fin m -> term n) (Delta : context m) :=
  forall x, Gamma |- sigma x ; subst (typeof x Delta) sigma.
Implicit Arguments satisfy [n m].
Notation "Gamma |= sigma ; Delta" := (satisfy Gamma sigma Delta) (at level 80).

Lemma Triv_satisfy : forall n : nat, forall Gamma : context n,
  valid Gamma -> Gamma |= id _ ; Gamma.
Proof.
unfold satisfy.
intros.
rewrite triv_subst.
apply Start_var.
assumption.
Qed.

Lemma Weak_satisfyl : forall n : nat, forall Delta : context n, forall m : nat, forall Gamma : context m, forall A : term m, forall sigma : (fin n -> term m), forall s : sort,
  Gamma |= sigma ; Delta -> Gamma |- A ; srt s ->
  ((Gamma, A) : context (S m)) |= (up (n:=m) (OO) sigma) ; Delta.
Proof.
unfold satisfy.
intros.
rewrite <- liftterm_subst.
apply weakening with (A := sigma x) (s := s); auto.
Qed.

Lemma Strength_satisfy : forall (m n : nat) (Gamma : context n) (Delta : context m) (sigma : fin (S m) -> term n) (A : term m),
  Gamma |= sigma ; (Delta, A) -> Gamma |= sigma (O) up (n:=m) ; Delta.
Proof.
unfold satisfy.
unfold comp at 1.
intros.
rewrite <- subst_liftterm.
apply H with (x := up x).
Qed.

Lemma satisfy_botsub : forall n (Gamma : context n) M A,
Gamma |- M ; A -> Gamma |= botsub M ; (Gamma, A).
Proof.
 intros.
 unfold satisfy.
 destruct x; simpl; rewrite subst_liftterm_botsub.
  apply Start_var.
    apply Context_Validity with M A.
    assumption.
  assumption.
Qed.