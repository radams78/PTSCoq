Require Export Terms.

(* The replacement operation, substituting variables for variables *)

Definition subvar : forall m : nat, term m -> forall n : nat, (fin m -> fin n) -> term n.
induction 1.
 intros m rho.
   exact (rho f).
 intros m rho.
   exact (srt s).
 intros m rho.
   exact (app (IHterm1 _ rho) (IHterm2 _ rho)).
 intros m rho.
   exact (pi (IHterm1 _ rho) (IHterm2 _ (Sfun rho))).
 intros m rho.
   exact (lda (IHterm1 _ rho) (IHterm2 _ (Sfun rho))).
Defined.
Implicit Arguments subvar [m n].

(* Results about subvar: *)

Lemma subvar_ext : forall m M n (rho sigma : fin m -> fin n), rho =f sigma -> subvar M rho = subvar M sigma.
Proof.
induction M; simpl; intros.
(* Variable *)
 apply var_wd.
   apply H.
(* Sort *)
 reflexivity.
(* Application *)
 apply app_wd.
  apply IHM1.
    assumption.
  apply IHM2.
    assumption.
(* Product *)
 apply pi_wd.
  apply IHM1.
    assumption.
  apply IHM2.
    apply Sfun_ext.
    assumption.
(* Abstraction *)
 apply lda_wd.
  apply IHM1.
    assumption.
  apply IHM2.
    apply Sfun_ext.
    assumption.
Qed.

Theorem subvar_lm : forall m M n p (rho : fin m -> fin n) (sigma : fin n -> fin p),
  subvar (subvar M rho) sigma = subvar M (sigma (O) rho).
Proof.
induction M; simpl; try reflexivity.
(* Application *)
 intros.
   apply app_wd.
  apply IHM1.
  apply IHM2.
(* Product *)
 intros.
   apply pi_wd.
  apply IHM1.
  rewrite IHM2.
    apply subvar_ext.
    apply funceq_sym.
    apply Sfun_comp.
(* Abstraction *)
 intros.
   apply lda_wd.
  apply IHM1.
  rewrite IHM2.
    apply subvar_ext.
    apply funceq_sym.
    apply Sfun_comp.
Qed.

Theorem triv_subvar : forall n (M : term n), subvar M (id _) = M.
Proof.
induction M; simpl; try reflexivity.
(* Application *)
 apply app_wd; assumption.
(* Product *)
 apply pi_wd.
  assumption.
  transitivity (subvar M2 (id _)).
   apply subvar_ext.
     apply Sfun_id.
   assumption.
(* Abstraction *)
 apply lda_wd.
  assumption.
  transitivity (subvar M2 (id _)).
   apply subvar_ext.
     apply Sfun_id.
   assumption.
Qed.

Lemma subvar_inj : forall m M N n (rho : fin m -> fin n),
  injective rho -> subvar M rho = subvar N rho -> M = N.
Proof.
induction M; destruct N; try discriminate 2; simpl.
(* Variable *)
 intros.
   apply var_wd.
   apply H.
   apply var_inj.
   assumption.
(* Sort *)
 intros.
   apply srt_wd.
   apply srt_inj with n0.
   assumption.
(* Application *)
 intros.
   apply app_wd.
  apply IHM1 with n0 rho.
   assumption.
   eapply app_injl.
     apply H0.
  apply IHM2 with n0 rho.
   assumption.
   eapply app_injr.
     apply H0.
(* Product *)
 intros.
   apply pi_wd.
  apply IHM1 with n0 rho.
   assumption.
   eapply pi_injl.
     apply H0.
  apply IHM2 with (S n0) (Sfun rho).
   apply Sfun_inj.
     assumption.
   eapply pi_injr.
     apply H0.
(* Abstraction *)
 intros.
   apply lda_wd.
  apply IHM1 with n0 rho.
   assumption.
   eapply lda_injl.
     apply H0.
  apply IHM2 with (S n0) (Sfun rho).
   apply Sfun_inj.
     assumption.
   eapply lda_injr.
     apply H0.
Qed.

(* How the form of M can be deduced from that of subvar M rho: *)
  
Lemma subvar_srt : forall m M n (rho : fin m -> fin n) s,
  subvar M rho = srt s -> M = srt s.
Proof.
destruct M; try discriminate 1.
intros.
apply srt_wd.
apply srt_inj with n0.
assumption.
Qed.

Lemma subvar_var : forall m M n (rho : fin m -> fin n) (x : fin n),
  subvar M rho = x -> exists y : fin m, M = y /\ x = rho y.
Proof.
destruct M; try discriminate 1.
intros.
split with f.
split.
 reflexivity.
 symmetry.
   apply var_inj.
   assumption.
Qed.

Lemma subvar_pi : forall m M n (rho : fin m -> fin n) A B,
  subvar M rho = pi A B -> exists A', exists B', M = pi A' B' /\ subvar A' rho = A /\ subvar B' (Sfun rho) = B.
Proof.
destruct M; try discriminate 1.
intros.
split with M1.
split with M2.
split.
 reflexivity.
 split.
  apply pi_injl with (subvar M2 (Sfun rho)) B.
    assumption.
  apply pi_injr with (subvar M1 rho) A.
    assumption.
Qed.

Lemma subvar_lda : forall m M n (rho : fin m -> fin n) A N,
  subvar M rho = lda A N -> exists A', exists N', M = lda A' N' /\ subvar A' rho = A /\ subvar N' (Sfun rho) = N.
Proof.
destruct M; try discriminate 1.
intros.
split with M1.
split with M2.
split.
 reflexivity.
 split.
  apply lda_injl with (subvar M2 (Sfun rho)) N.
    assumption.
  apply lda_injr with (subvar M1 rho) A.
    assumption.
Qed.

Lemma subvar_app : forall m M n (rho : fin m -> fin n) N P,
  subvar M rho = app N P -> exists N', exists P', M = app N' P' /\ subvar N' rho = N /\ subvar P' rho = P.
Proof.
destruct M; try discriminate 1.
intros.
split with M1.
split with M2.
split.
 reflexivity.
 split.
  apply app_injl with (subvar M2 rho) P.
    assumption.
  apply app_injr with (subvar M1 rho) N.
    assumption.
Qed.

(* The lifting of a term from term n to term (S n) *)

Definition liftterm n (M : term n) : term (S n) := subvar M (up (n:=n)).
Implicit Arguments liftterm [n].

Lemma liftterm_srt : forall n (M : term n) s,
  liftterm M = srt s -> M = srt s.
Proof.
intros n M.
exact (subvar_srt _ _ _ _).
Qed.

Lemma liftterm_var : forall n (M : term n) (x : fin (S n)),
  liftterm M = x -> exists y : fin n, M = y /\ eq (A := fin (S n)) x (up y).
Proof.
intros n M.
exact (subvar_var _ _ _ _).
Qed.

Lemma liftterm_pi : forall n (M : term n) A B,
  liftterm M = pi A B -> exists A', exists B', M = pi A' B' /\ liftterm A' = A /\ subvar B' (Sfun (up (n := n))) = B.
Proof.
intros n M.
exact (subvar_pi _ _ _ _).
Qed.

Lemma liftterm_lda : forall n (M : term n) A N,
  liftterm M = lda A N -> exists A', exists N', M = lda A' N' /\ liftterm A' = A /\ subvar N' (Sfun (up (n := n))) = N.
Proof.
intros n M.
exact (subvar_lda _ _ _ _).
Qed.

Lemma liftterm_app : forall n (M : term n) N P,
  liftterm M = app N P -> exists N', exists P', M = app N' P' /\ liftterm N' = N /\ liftterm P' = P.
Proof.
intros n M.
exact (subvar_app _ _ _ _).
Qed.

Lemma liftterm_subvar : forall m n M (rho : fin m -> fin n),
  liftterm (subvar M rho) = subvar M (up (n:=n) (O) rho).
Proof.
intros.
unfold liftterm.
apply subvar_lm.
Qed.

Lemma subvar_liftterm : forall m n M (rho : fin (S m) -> fin n),
  subvar (liftterm M) rho = subvar M (rho (O) up (n:=m)).
Proof.
intros.
unfold liftterm.
apply subvar_lm.
Save.

Lemma liftterm_subvar' : forall m n M (rho : fin m -> fin n),
  liftterm (subvar M rho) = subvar (liftterm M) (Sfun rho).
Proof.
intros.
rewrite subvar_liftterm.
apply liftterm_subvar with (rho := rho).
Qed.

Lemma liftterm_liftterm : forall n (M : term n), liftterm (liftterm M) = subvar M (up (n:=S n) (O) up (n:=n)).
Proof.
intros.
apply subvar_liftterm with (M := M) (rho := up (n:=S n)).
Qed.

Lemma liftterm_liftterm' : forall n (M : term n), liftterm (liftterm M) = subvar (liftterm M) (Sfun (up (n:=n))).
Proof.
unfold liftterm at 2.
intros.
apply liftterm_subvar' with (rho := up (n:=n)).
Qed.

Lemma liftterm_inj : forall n (M N : term n), liftterm M = liftterm N -> M = N.
Proof.
unfold liftterm.
intros n M N.
apply subvar_inj.
exact (up_inj n).
Qed.

(* Lifting of Substitutions *)

Definition liftsub m n (rho : fin m -> term n) := fun x : fin (S m) =>
  match x return (term (S n)) with
  | None => bot
  | Some x0 => liftterm (rho x0)
  end.
Implicit Arguments liftsub [m n].

Lemma liftsub_ext : forall m n (rho sigma : fin m -> term n), rho =f sigma -> liftsub rho =f liftsub sigma.
Proof.
unfold funceq.
destruct x; simpl.
 rewrite H.
   reflexivity.
 reflexivity.
Qed.

Lemma liftsub_id : forall n, liftsub (n:=n) (id _) =f id _.
Proof.
unfold funceq.
destruct x; auto.
Qed.

Lemma liftsub_comp : forall m n p (rho : fin m -> fin n) (sigma : fin n -> term p), liftsub (sigma (O) rho) =f (liftsub sigma (O) Sfun rho).
Proof.
unfold funceq.
destruct x; auto.
Qed.

Lemma Sfun_is_liftsub : forall m n (rho : fin m -> fin n), (var (n:=S n) (O) Sfun rho) =f liftsub (var (n:=n) (O) rho).
Proof.
unfold funceq.
destruct x; auto.
Qed.

(* Composition of functions fin m -> term n and fin n -> fin p *)

Definition Comp m n p (sigma : fin n -> fin p) (rho : fin m -> term n) := fun x => subvar (rho x) sigma.
Implicit Arguments Comp [m n p].
Notation "f (OO) g" := (Comp f g) (at level 50).

Lemma liftsub_Comp : forall m n p (rho : fin m -> term n) (sigma : fin n -> fin p), (Sfun sigma (OO) liftsub rho) =f liftsub (sigma (OO) rho).
Proof.
unfold funceq.
destruct x; simpl.
 unfold Comp.
   simpl.
   rewrite subvar_liftterm.
   rewrite liftterm_subvar.
   reflexivity.
 reflexivity.
Qed.

Lemma Comp_is_comp : forall m n p (rho : fin m -> fin n) (sigma : fin n -> fin p), sigma (OO) (fun x => rho x) = sigma (O) rho.
Proof.
reflexivity.
Qed.
