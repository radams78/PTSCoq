(* Finite.v --- Finite Types whose objects will be used as variables *)

(* Preliminaries *)

Definition funceq (X Y : Set) (f g : X -> Y) := forall x : X, f x = g x.
Implicit Arguments funceq [X Y].
Notation "f =f g" := (funceq f g) (at level 80).

Lemma funceq_ref : forall (X Y : Set) (f : X -> Y), f =f f.
Proof.
unfold funceq.
reflexivity.
Qed.

Lemma funceq_sym : forall (X Y : Set) (f g : X -> Y), f =f g -> g =f f.
Proof.
unfold funceq.
auto.
Qed.

Lemma funceq_trans : forall (X Y : Set) (f g h : X -> Y), f =f g -> g =f h -> f =f h.
Proof.
unfold funceq.
intros.
transitivity (g x); auto.
Qed.

Definition id (X : Set) := fun x : X => x.

Definition comp (X Y Z : Set) (g : Y -> Z) (f : X -> Y) := fun x => g (f x).
Implicit Arguments comp [X Y Z].
Notation "f (O) g" := (comp f g) (at level 50).

Definition injective (X Y : Set) (f : X -> Y) := forall x y, f x = f y -> x = y.
Implicit Arguments injective [X Y].

(* Option Types *)

Lemma Some_inj : forall (X : Set) (x y : X), Some x = Some y -> x = y.
Proof.
injection 1.
auto.
Qed.

Lemma option_disc : forall (X : Set) (x : X), (Some x = None) -> False.
Proof.
discriminate 1. 
Qed. 

(* The family of finite types *)

Fixpoint fin (n : nat) {struct n} : Set :=
  match n with
  | O => Empty_set
  | S m => option (fin m)
  end.

Definition bot n : fin (S n) := None.
Implicit Arguments bot [n].
Definition up n x : fin (S n) := Some x.
Implicit Arguments up [n].

Lemma up_wd : forall n (x y : fin n), x = y -> up x = up y.
Proof.
intro n.
apply f_equal.
Qed.

Lemma up_inj : forall n (x y : fin n), up x = up y -> x = y.
Proof.
intro n.
apply Some_inj with (X := fin n).
Qed.

Definition Sfun m n (f : fin m -> fin n) := fun x : fin (S m) =>
  match x with
  | None => bot
  | Some y => up (f y)
  end.
Implicit Arguments Sfun [m n].

Lemma Sfun_ext : forall m n (rho sigma : fin m -> fin n), rho =f sigma -> Sfun rho =f Sfun sigma.
Proof.
unfold funceq.
destruct x; simpl.
 apply up_wd with (n:=n).
   apply H.
 reflexivity.
Qed.

Lemma Sfun_inj : forall m n (rho : fin m -> fin n), injective rho -> injective (Sfun rho).
Proof.
intros m n rho rho_inj x.
case x; clear x; fold fin.
 intros x y.
   case y; clear y; fold fin; simpl.
  intro y.
    injection 1.
    intro rho_x_is_rho_y.
    rewrite rho_inj with x y; auto.
  discriminate 1.
 intro y.
   case y; clear y; fold fin; simpl.
  discriminate 1.
  reflexivity.
Qed.

Lemma Sfun_id : forall n, Sfun (id (fin n)) =f id _.
Proof.
unfold funceq.
destruct x; auto.
Qed.

Lemma Sfun_comp : forall m n p (rho : fin m -> fin n) (sigma : fin n -> fin p),
 Sfun (sigma (O) rho) =f Sfun sigma (O) Sfun rho.
Proof.
unfold funceq.
destruct x; reflexivity.
Qed.