Require Export Subvar.

(* Definition of Substitution *)

Definition subst : forall m, term m -> forall n, (fin m -> term n) -> term n.
  induction 1.
  intros m rho.
    exact (rho f).
  intros m rho.
    exact (srt s).
  intros m rho.
    exact (app (IHterm1 _ rho) (IHterm2 _ rho)).
  intros m rho.
    exact (pi (IHterm1 _ rho) (IHterm2 _ (liftsub rho))).
  intros m rho.
    exact (lda (IHterm1 _ rho) (IHterm2 _ (liftsub rho))).
Defined.
Implicit Arguments subst [m n].

Lemma subst_ext : forall m M n (rho sigma : fin m -> term n),
  rho =f sigma -> subst M rho = subst M sigma.
Proof.
induction M; simpl; auto.
(* Application *)
 intros.
   apply app_wd; auto.
(* Product *)
 intros.
   apply pi_wd; auto.
   apply IHM2. 
   apply liftsub_ext.
   assumption.
(* Abstraction *)
 intros.
   apply lda_wd; auto.
   apply IHM2.
   apply liftsub_ext.
   assumption.
Qed.

Theorem triv_subst : forall n (M : term n), subst M (id _) = M.
Proof.
induction M; simpl; auto.
(* Application *)
apply app_wd; auto.
(* Product *)
apply pi_wd; auto.
  transitivity (subst M2 (id _)).
  apply subst_ext.
    apply liftsub_id.
  assumption.
(* Abstraction *)
apply lda_wd; auto.
  transitivity (subst M2 (id _)).
  apply subst_ext.
    apply liftsub_id.
  assumption.
Qed.

Theorem triv_subst' n (M : term n) : subst M (var (n:=n)) = M.
intros.
rewrite subst_ext with n M n (var (n:=n)) (fun x : fin n => var x).
 apply triv_subst.
 intro.
   reflexivity.
Qed.

(* Results connecting subst and subvar *)

Lemma subst_subvar : forall m M n p (rho : fin m -> fin n) (sigma : fin n -> term p),
  subst (subvar M rho) sigma = subst M (sigma (O) rho).
Proof.
induction M; simpl; try reflexivity.
(* Application *)
intros.
  apply app_wd; auto.
(* Product *)
intros.
  apply pi_wd; auto.
  rewrite IHM2.
  apply subst_ext.
  apply funceq_sym.
  apply liftsub_comp.
(* Abstraction *)
intros.
  apply lda_wd; auto.
  rewrite IHM2.
  apply subst_ext.
  apply funceq_sym.
  apply liftsub_comp.
Qed.

Lemma subvar_subst : forall m M n p (rho : fin m -> term n) (sigma : fin n -> fin p),
  subvar (subst M rho) sigma = (subst M (sigma (OO) rho)).
Proof.
induction M; simpl; auto.
(* Application *)
intros.
  apply app_wd; auto.
(* Product *)
intros.
  apply pi_wd; auto.
  rewrite IHM2.
  apply subst_ext.
  apply liftsub_Comp.
(* Abstraction *)
intros.
  apply lda_wd; auto.
  rewrite IHM2.
  apply subst_ext.
  apply liftsub_Comp.
Qed.
      
Lemma subst_is_subvar : forall m M n (rho : fin m -> fin n),
  subst M (var (n:=n) (O) rho) = subvar M rho.
Proof.
induction M; simpl; auto.
(* Application *)
intros.
  apply app_wd; auto.
(* Product *)
intros.
  apply pi_wd; auto.
  rewrite <- IHM2.
  apply subst_ext.
  apply funceq_sym.
  apply Sfun_is_liftsub.
(* Abstraction *)
intros.
  apply lda_wd; auto.
  rewrite <- IHM2.
  apply subst_ext.
  apply funceq_sym.
  apply Sfun_is_liftsub.
Qed.

(* Results about subst and liftterm *)

Lemma subst_liftterm : forall m M n (sigma : fin (S m) -> term n),
  subst (liftterm M) sigma = subst M (sigma (O) up (n:=m)).
Proof.
intros.
unfold liftterm.
apply subst_subvar.
Qed.

Lemma liftterm_subst : forall m M n (sigma : fin m -> term n),
  liftterm (subst M sigma) = subst M (up (n:=n) (OO) sigma).
Proof.
unfold liftterm.
intros.
apply subvar_subst.
Save.

Lemma liftterm_subst' : forall m n M (sigma : fin m -> term n),
  liftterm (subst M sigma) = subst (liftterm M) (liftsub sigma).
Proof.
intros.
rewrite subst_liftterm.
apply liftterm_subst with (sigma := sigma).
Qed.

(* Composition of Functions fin m -> term n and fin n -> term p *)

Definition CComp m n p (rho : fin n -> term p) (sigma : fin m -> term n) := fun x => subst (sigma x) rho.
Implicit Arguments CComp [m n p].
Notation "rho [] sigma" := (CComp rho sigma) (at level 50).

Lemma liftsub_CComp : forall m n p (rho : fin n -> term p) (sigma : fin m -> term n), liftsub (rho [] sigma) =f (liftsub rho [] liftsub sigma).
Proof.
unfold funceq.
destruct x; simpl.
unfold CComp.
  simpl.
  rewrite liftterm_subst.
  rewrite subst_liftterm.
  reflexivity.
reflexivity.
Qed.

Lemma CComp_is_Comp : forall m n p (sigma : fin n -> fin p) (rho : fin m -> term n), (fun x => sigma x) [] rho =f sigma (OO) rho.
Proof.
unfold funceq.
unfold CComp.
unfold Comp.
intros.
apply subst_is_subvar with (rho := sigma).
Qed.

(* The Substitution Lemma *)

Theorem subst_lm : forall m M n p (rho : fin m -> term n) (sigma : fin n -> term p),
  subst (subst M rho) sigma = subst M (sigma [] rho).
Proof.
induction M; simpl; auto.
(* Application *)
intros.
  apply app_wd; auto.
(* Abstraction *)
intros.
  apply pi_wd; auto.
  rewrite IHM2.
  apply subst_ext.
  apply funceq_sym.
  apply liftsub_CComp.
(* Application *)
intros.
  apply lda_wd; auto.
  rewrite IHM2.
  apply subst_ext.
  apply funceq_sym.
  apply liftsub_CComp.
Qed.

(* The special case subbot --- substituting a given term for bot, and x for up x *)

Definition botsub n (N : term n) := fun x : fin (S n) =>
  match x return term n with
  | None => N
  | Some y => var y
  end.
Implicit Arguments botsub [n].

Lemma botsub_up n (M : term n) : botsub M (O) up (n:=n) =f var (n:=n).
Proof.
intros.
intro x.
reflexivity.
Qed.

Lemma botsub_Sfun : forall m n (N : term m) (rho : fin m -> fin n),
  rho (OO) botsub N =f botsub (subvar N rho) (O) Sfun rho.
Proof.
unfold funceq.
destruct x; auto.
Qed.

Lemma botsub_liftsub : forall m n (N : term m) (rho : fin m -> term n),
  rho [] botsub N =f botsub (subst N rho) [] liftsub rho.
Proof.
unfold funceq.
destruct x.
 unfold CComp.
   simpl.
   rewrite subst_liftterm.
   symmetry.
   apply triv_subst with (M := rho f).
 reflexivity.
Qed.

Definition subbot n M (N : term n) := subst M (botsub N).
Implicit Arguments subbot [n].

Lemma subvar_subbot : forall (m n : nat) (M : term (S m)) (N : term m) (rho : fin m -> fin n),
  subvar (subbot M N) rho = subbot (subvar M (Sfun rho)) (subvar N rho).
Proof.
intros.
unfold subbot.
rewrite subst_subvar.
rewrite subvar_subst.
apply subst_ext.
apply botsub_Sfun.
Qed.

Lemma liftterm_subbot : forall (n : nat) (M : term (S n)) (N : term n),
  liftterm (subbot M N) = subbot (subvar M (Sfun (up (n := n)))) (liftterm N).
Proof.
intros.
unfold liftterm.
apply subvar_subbot with (rho := up (n := n)).
Save.

Lemma subbot_subvar : forall m M n (rho : fin m -> fin (S n)) N,
  subbot (subvar M rho) N = subst M (botsub N (O) rho).
Proof.
intros.
unfold subbot.
apply subst_subvar.
Qed.

Lemma subst_subbot : forall (m n : nat) (M : term (S n)) (N : term n) (rho : fin n -> term m),
  subst (subbot M N) rho = subbot (subst M (liftsub rho)) (subst N rho).
Proof.
intros.
unfold subbot.
repeat rewrite subst_lm.
apply subst_ext.
apply botsub_liftsub.
Qed.

Lemma subst_liftterm_botsub : forall n (M N : term n),
  subst (liftterm M) (botsub N) = M.
Proof.
intros.
rewrite subst_liftterm.
apply triv_subst with (M := M).
Qed.

Lemma subbot_liftterm : forall n (M N : term n), subbot (liftterm M) N = M.
Proof.
exact subst_liftterm_botsub.
Qed.