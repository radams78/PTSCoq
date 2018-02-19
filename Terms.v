Require Export Finite.

(* Grammar of a PTS *)

Parameter sort : Set.

Inductive term : nat -> Set :=
  var :> forall n, fin n -> term n |
  srt : forall n, sort -> term n |
  app : forall n, term n -> term n -> term n |
  pi : forall n, term n -> term (S n) -> term n |
  lda : forall n, term n -> term (S n) -> term n.
Implicit Arguments var [n].
Implicit Arguments srt [n].
Implicit Arguments app [n].
Implicit Arguments pi [n].
Implicit Arguments lda [n].

(* Destructors for the types term n *)
(* These functions are only needed to prove the injectivity results below *)

Definition antivar n (M : term n) :=
match M in (term n) return (option (fin n)) with
| var n x   => Some x
| srt _ _   => None
| app _ _ _ => None
| pi  _ _ _ => None
| lda _ _ _ => None
end.
Implicit Arguments antivar [n].

Definition appleft n (M : term n) :=
match M in (term n) return (term n) with
| var n x   => x
| srt n s   => srt s
| app n P _ => P
| pi  n A B => pi A B
| lda n A P => lda A P
end.
Implicit Arguments appleft [n].

Definition appright n (M : term n) :=
match M in (term n) return (term n) with
| var n x   => x
| srt n s   => srt s
| app n _ Q => Q
| pi  n A B => pi A B
| lda n A P => lda A P
end.
Implicit Arguments appright [n].

Definition quantleft n (M : term n) :=
match M in (term n) return (term n) with
| var n x   => x
| srt n s   => srt s
| app n P Q => app P Q
| pi  n A B => A
| lda n A P => A
end.
Implicit Arguments quantleft [n].

Definition quantright n (M : term n) :=
match M in (term n) return (term (S n)) with
| var n x   => bot
| srt n s   => bot
| app n P Q => bot
| pi  n A B => B
| lda n A P => P
end.
Implicit Arguments quantright [n].

(* Well-definition and injectivity results for the constructors for term *)

Lemma var_wd : forall n (x y : fin n), x = y -> var x = var y.
Proof.
intro n.
apply f_equal.
Qed.

Lemma var_inj : forall n (x y : fin n), var x = var y -> x = y.
Proof.
intros.
apply Some_inj.
change (Some x) with (antivar x).
change (Some y) with (antivar y).
apply f_equal with (term n).
assumption.
Qed.

Lemma srt_wd : forall n s t, s = t -> srt (n := n) s = srt t.
Proof.
intro n.
apply f_equal.
Qed.

Lemma srt_inj : forall n s t, srt (n := n) s = srt t -> s = t.
Proof.
injection 1.
auto.
Qed.

Lemma app_wd : forall n (M M' N N' : term n), M = M' -> N = N' -> app M N = app M' N'.
Proof.
intro n.
apply f_equal2.
Qed.

Lemma app_injl : forall n (M M' N N' : term n), app M N = app M' N' -> M = M'.
Proof.
intros n M M' N N'.
change M at 2 with (appleft (app M N)).
change M' at 2 with (appleft (app M' N')).
apply f_equal.
Qed.

Lemma app_injr : forall n (M M' N N' : term n), app M N = app M' N' -> N = N'.
Proof.
intros n M M' N N'.
change N at 2 with (appright (app M N)).
change N' at 2 with (appright (app M' N')).
apply f_equal.
Qed.

Lemma pi_wd : forall n (A A' : term n) (B B' : term (S n)), A = A' -> B = B' -> pi A B = pi A' B'.
Proof.
intro n.
apply f_equal2.
Qed.

Lemma pi_injl : forall n (A A' : term n) (B B' : term (S n)), pi A B = pi A' B' -> A = A'.
Proof.
intros n A A' B B'.
change A at 2 with (quantleft (pi A B)).
change A' at 2 with (quantleft (pi A' B')).
apply f_equal.
Qed.

Lemma pi_injr : forall n (A A' : term n) (B B' : term (S n)), pi A B = pi A' B' -> B = B'.
Proof.
intros n A A' B B'.
change B at 2 with (quantright (pi A B)).
change B' at 2 with (quantright (pi A' B')).
apply f_equal.
Qed.

Lemma lda_wd : forall n (A A' : term n) (M M' : term (S n)), A = A' -> M = M' -> lda A M = lda A' M'.
Proof.
intro n.
apply f_equal2.
Qed.

Lemma lda_injl : forall n (A A' : term n) (M M' : term (S n)), lda A M = lda A' M' -> A = A'.
Proof.
intros n A A' M M'.
change A at 2 with (quantleft (lda A M)).
change A' at 2 with (quantleft (lda A' M')).
apply f_equal.
Qed.

Lemma lda_injr : forall n (A A' : term n) (M M' : term (S n)), lda A M = lda A' M' -> M = M'.
Proof.
intros n A A' M M'.
change M at 2 with (quantright (lda A M)).
change M' at 2 with (quantright (lda A' M')).
apply f_equal.
Qed.
