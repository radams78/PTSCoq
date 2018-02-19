Require Import Arith.
Require Export PTS.
Require Import CR.
Require Import Meta.

Lemma lt_eq_lt_lm : forall n, (lt_eq_lt_dec n n) = (inleft (n < n) (right (n < n) (refl_equal n))).
Proof.
 induction n; simpl.
  reflexivity.
  rewrite IHn.
    simpl.
    reflexivity.
Qed.

Inductive string (m : nat) : nat -> Set :=
  emp : string m m |
  cons : forall n : nat, term n -> string m (S n) -> string m n.

Implicit Arguments emp [m].
Implicit Arguments cons [m n].

Lemma string_leq : forall m n, string m n -> le n m.
Proof.
  induction 1.
   auto.
   apply le_trans with (S n); auto.
Qed.

Definition head : forall m n, string m n -> lt n m -> term n.
  induction 1.
   intro.
     elim lt_irrefl with m.
     assumption.
   intro.
     assumption.
Defined.

Implicit Arguments head [m n].

Lemma head_wd : forall m n (Delta : string m n) l l', head Delta l = head Delta l'.
Proof.
  induction Delta; simpl.
   intro l.
     elim lt_irrefl with m.
     assumption.
   reflexivity.
Qed.

Definition tail : forall m n, string m n -> lt n m -> string m (S n).
 induction 1.
  intro.
    elim lt_irrefl with m.
    assumption.
  intro.
    assumption.
Defined.

Implicit Arguments tail [m n].

Lemma tail_wd : forall m n (Delta : string m n) l l', tail Delta l = tail Delta l'.
Proof.
 induction Delta; simpl.
  intro.
    elim lt_irrefl with m.
    assumption.
  reflexivity.
Qed.

Definition string_id : forall m n, string m n -> string m n.
 Proof.
  intros m n Delta.
  case (lt_eq_lt_dec m n).
  destruct 1.
   elim lt_not_le with m n.
    assumption.
    apply string_leq.
      assumption.
   rewrite e.
     exact emp.
   intro.
     exact (cons (head Delta l) (tail Delta l)).
Defined.

Implicit Arguments string_id [m n].

Lemma string_id_is_id : forall m n (Delta : string m n), Delta = string_id Delta.
Proof.
 induction Delta; unfold string_id.
  rewrite lt_eq_lt_lm with m.
    reflexivity.
  case (lt_eq_lt_dec m n).
  destruct s.
   elim (lt_not_le m n l (string_leq m n (cons t Delta))).
   elim le_Sn_n with n.
     apply le_trans with m.
      apply string_leq.
	assumption.
      rewrite e.
	auto.
   reflexivity.
Qed.

Lemma string_n_n : forall n (Delta : string n n), Delta = emp.
Proof.
 intros.
 rewrite string_id_is_id with n n Delta.
 unfold string_id.
 rewrite lt_eq_lt_lm with n.
 reflexivity.
Qed.

Lemma string_m_n : forall m n (Delta : string m n) l, Delta = cons (head Delta l) (tail Delta l).
Proof.
 intros.
 transitivity (string_id Delta).
  apply string_id_is_id.
  unfold string_id.
    case (lt_eq_lt_dec m n).
    destruct s.
     elim (lt_not_le m n l0 (string_leq m n Delta)).
     absurd (n < m).
      rewrite e.
        apply lt_irrefl.
      assumption.
     intro l'.
       rewrite head_wd with m n Delta l' l.
       rewrite tail_wd with m n Delta l' l.
       reflexivity.
Qed.

Definition red_string : forall m n, string m n -> string m n -> Prop.
 induction 1.
  intro.
    exact True.
  intro Delta'.
    exact (red t (head Delta' (string_leq m (S n) H)) /\ IHstring (tail Delta' (string_leq m (S n) H))).
Defined.

Implicit Arguments red_string [m n].
Notation "Delta ->>ss Delta'" := (red_string Delta Delta') (at level 80).

Lemma red_string_ref : forall m n (Delta : string m n), Delta ->>ss Delta.
Proof.
 induction Delta; split; auto.
Qed.

Definition Pi : forall m n, string m n -> term m -> term n.
 induction 1.
  auto.
  intro B. 
    exact (pi t (IHstring B)).
Defined.

Implicit Arguments Pi [m n].

Lemma red_Pi_inv : forall m n (Delta : string m n) A B, red (Pi Delta A) B ->
  exists Delta', exists A', Delta ->>ss Delta' /\ A ->> A' /\ B = Pi Delta' A'.
Proof.
 induction Delta; intros.
  split with (emp (m:=m)).
    split with B.
    split.
     split.
    split; auto.
  elim Gen_red_pi with n t (Pi Delta A) B.
   intro t'.
     destruct 1.
     rename x into C.
     destruct H0.
     destruct H1.
     elim IHDelta with A C.
      intro Delta0.
        destruct 1.
        rename x into A'.
	destruct H3.
	destruct H4.
	split with (cons t' Delta0).
	split with A'.
	split.
	  split; assumption.
	split.
	 assumption.
         rewrite H0.
           rewrite H5.
           reflexivity.
      assumption.
   assumption.
Qed.

Definition Lda : forall m n, string m n -> term m -> term n.
 induction 1.
  auto.
  intro B.
    exact (lda t (IHstring B)).
Defined.

Implicit Arguments Lda [m n].

Definition concat : forall m n, context n -> string m n -> context m.
 induction 2.
   assumption.
   exact (IHstring (H,t)).
Defined.

Implicit Arguments concat [m n].
Notation "Gamma @ Delta" := (concat Gamma Delta) (at level 60).

Lemma ctxt_strng : forall m n Gamma (Theta : string m n) , valid (Gamma @ Theta) -> valid Gamma.
Proof.
 induction Theta; simpl.
  auto.
  intro.
    elim (IHTheta (Gamma, t)).
     intro s.
       apply Context_Validity.
     assumption.
Qed.

Inductive mtch (m p : nat) : nat -> nat -> Set :=
  mtchO : mtch m p m p |
  mtchS : forall (n q : nat), mtch m p (S n) (S q) -> mtch m p n q.

Implicit Arguments mtchO [m p].
Implicit Arguments mtchS [m p n q].

Lemma mtch_leql : forall m p n q, mtch m p n q -> le n m.
Proof.
 induction 1.
   auto.
   apply le_trans with (S n); auto.
Qed.

Lemma mtch_leqr : forall m p n q, mtch m p n q -> le q p.
Proof.
 induction 1.
   auto.
   apply le_trans with (S q); auto.
Qed.

Lemma mtch_Sm_Sn : forall m n, string m n -> mtch m (S m) n (S n).
Proof.
 induction 1.
  exact mtchO.
  apply mtchS.
    assumption.
Qed.

Lemma pre_mtch_Sm_Sn' : forall m' n', string m' n' -> forall m n, m' = S m -> n' = S n -> mtch m (S m) n (S n).
Proof.
 induction 1.
  intros.
    replace n with m.
     exact mtchO.
     apply eq_add_S.
       transitivity m'; auto.
  intros.
    apply mtchS.
    apply IHstring; auto.
Qed.

Lemma mtch_Sm_Sn' : forall m n, string (S m) (S n) -> mtch m (S m) n (S n).
Proof.
 intros.
 apply pre_mtch_Sm_Sn' with (S m) (S n); auto.
Qed.

Lemma pre_mtch_Sm_Sn_inv : forall m' n', string m' n' -> forall m n, m' = S m -> n' = S n -> mtch (S m) m (S n) n.
Proof.
 induction 1.
  intros.
    replace n with m.
     exact mtchO.
     apply eq_add_S.
       transitivity m'; auto.
  intros.
    apply mtchS.
    apply IHstring; auto.
Qed.

Lemma mtch_Sm_Sn_inv : forall m n, string (S m) (S n) -> mtch (S m) m (S n) n.
Proof.
 intros.
 apply pre_mtch_Sm_Sn_inv with (S m) (S n); auto.
Qed.

Definition strsubvar : forall m p n q, mtch m p n q -> string m n -> (fin n -> fin q) -> string p q.
 induction 1.
  intros.
    exact emp.
  intros Delta rho.
    exact (cons (subvar (head Delta (mtch_leql _ _ _ _ H)) rho) (IHmtch (tail Delta (mtch_leql _ _ _ _ H)) (Sfun rho))).
Defined.

Implicit Arguments strsubvar [m p n q].
  
Definition liftstring m n (Delta : string m n) := strsubvar (mtch_Sm_Sn _ _ Delta) Delta (up (n:=n)).

Implicit Arguments liftstring [m n].

Definition subvar_lift : forall m p n q, mtch m p n q -> (fin n -> fin q) -> fin m -> fin p.
 induction 1.
  auto.
  intro rho.
    exact (IHmtch (Sfun rho)).
Defined.

Implicit Arguments subvar_lift [m p n q].

Lemma valid_concat : forall m p n q (e : mtch m p n q) Gamma Delta rho Theta,
  subctxt Gamma Delta rho -> valid (Gamma @ Theta) -> valid Delta -> valid (Delta @ strsubvar e Theta rho).
Proof.
 induction e; simpl.
  auto.
  intros.
    rewrite string_m_n with m n Theta (mtch_leql _ _ _ _ e) in H0.
    apply IHe with (Gamma, head Theta (mtch_leql _ _ _ _ e)).
     apply Weak_subctxt; assumption.
     assumption.
     elim (ctxt_strng _ (S n) (Gamma, head Theta (mtch_leql _ _ _ _ e)) (tail Theta (mtch_leql _ _ _ _ e))).
      intros s H2.
        split with s.
        apply Weakening with (Delta := Gamma) (A := srt (n:=n) s) (rho := rho); assumption.
      assumption.
Qed.

Lemma Pi_subvar : forall m p n q (e : mtch m p n q) Delta B rho,
  subvar (Pi Delta B) rho = Pi (strsubvar e Delta rho) (subvar B (subvar_lift e rho)).
Proof.
 induction e; simpl.
  intro Delta.
    rewrite string_n_n with m Delta.
    simpl.
    reflexivity.
  intros Delta B rho.
    rewrite string_m_n with m n Delta (mtch_leql _ _ _ _ e).
    simpl.
    rewrite IHe.
    reflexivity.
Qed.

Lemma Lda_subvar : forall m p n q (e : mtch m p n q) Delta M rho,
  subvar (Lda Delta M) rho = Lda (strsubvar e Delta rho) (subvar M (subvar_lift e rho)).
Proof.
 induction e; simpl.
  intro Delta.
    rewrite string_n_n with m Delta.
    simpl.
    reflexivity.
  intros Delta B rho.
    rewrite string_m_n with m n Delta (mtch_leql _ _ _ _ e).
    simpl.
    rewrite IHe.
    reflexivity.
Qed.

Lemma subctxt_concat : forall m p n q (e : mtch m p n q) Gamma Delta rho Theta,
  subctxt Gamma Delta rho -> subctxt (Gamma @ Theta) (Delta @ strsubvar e Theta rho) (subvar_lift e rho).
Proof.
 induction e; simpl.
  intros.
    rewrite string_n_n with m Theta.
    assumption.
  intros.
    replace (Gamma @ Theta) with (((Gamma, head Theta (mtch_leql _ _ _ _ e)) : context (S n)) @ tail Theta (mtch_leql _ _ _ _ e)).
     apply IHe.
       apply Weak_subctxt.
       assumption.
     rewrite string_m_n with m n Theta (mtch_leql _ _ _ _ e).
       reflexivity.
Qed.

Lemma Pi_subvar_inv : forall m p n q (e : mtch m p n q) Delta M B rho, subvar M rho = Pi Delta B -> 
  exists Delta', exists B', M = Pi Delta' B' /\ Delta = strsubvar e Delta' rho /\ B = subvar B' (subvar_lift e rho).
Proof.
 induction e; simpl.
  intro Delta.
    rewrite string_n_n with p Delta.
    simpl.
    intros.
    split with (emp (m:=m)).
    simpl.
    split with M.
    auto.
  intro Delta.
    rewrite string_m_n with p q Delta (mtch_leqr m p (S n) (S q) e).
    simpl.
    intros.
    elim subvar_pi with n M q rho (head Delta (mtch_leqr m p (S n) (S q) e)) (Pi (tail Delta (mtch_leqr m p (S n) (S q) e)) B).
     intro A'.
       destruct 1.
       rename x into B'.
       destruct H0.
       destruct H1.
       elim IHe with (tail Delta (mtch_leqr m p (S n) (S q) e)) B' B (Sfun rho).
        intro Delta0.
	  destruct 1.
	  rename x into B0.
	  destruct H3.
	  destruct H4.
	  split with (cons A' Delta0).
	  split with B0.
	  split; simpl.
	   rewrite <- H3.
	     assumption.
	  split.
	   rewrite H4.
	     rewrite <- H1.
	     reflexivity.
	   assumption.
	assumption.  
     assumption.
Qed.

Lemma red_subvar_Pi : forall m p n q (e : mtch m p n q) M rho Delta B,
  subvar M rho ->> Pi Delta B -> exists Delta', exists B',
  Delta = strsubvar e Delta' rho /\ B = subvar B' (subvar_lift e rho) /\ M ->> Pi Delta' B'.
Proof.
 intros.
 elim red_subvar_inv with n q M rho (Pi Delta B).
  intro M'.
    destruct 1.
    elim Pi_subvar_inv with m p n q e Delta M' B rho.
     intro Delta'.
       destruct 1.
       rename x into B'.
       destruct H2.
       destruct H3.
       split with Delta'.
       split with B'.
       split.
        assumption.
       split.
        assumption.
	rewrite <- H2.
	  assumption.
     auto.
  assumption.
Qed.

Definition strsubst : forall m p n q, mtch m p n q -> string m n -> (fin n -> term q) -> string p q.
 induction 1.
  intros.
    exact emp.
  intros Delta rho.
    exact (cons (subst (head Delta (mtch_leql _ _ _ _ H)) rho) (IHmtch (tail Delta (mtch_leql _ _ _ _ H)) (liftsub rho))).
Defined.

Implicit Arguments strsubst [m p n q].

Definition subst_lift : forall m p n q, mtch m p n q -> (fin n -> term q) -> fin m -> term p.
 induction 1.
  auto.
  intro rho.
    exact (IHmtch (liftsub rho)).
Defined.

Implicit Arguments subst_lift [m p n q].

Lemma Pi_subst : forall m p n q (e : mtch m p n q) Delta B rho,
  subst (Pi Delta B) rho = Pi (strsubst e Delta rho) (subst B (subst_lift e rho)).
Proof.
 induction e; simpl.
  intro Delta.
    rewrite string_n_n with m Delta.
    reflexivity.
  intros.
    rewrite string_m_n with m n Delta (mtch_leql _ _ _ _ e).
    simpl.
    rewrite IHe.
    reflexivity.
Qed.

Lemma Lda_subst : forall m p n q (e : mtch m p n q) Delta B rho,
  subst (Lda Delta B) rho = Lda (strsubst e Delta rho) (subst B (subst_lift e rho)).
Proof.
 induction e; simpl; intros.
  rewrite string_n_n with m Delta.
    reflexivity.
  rewrite string_m_n with m n Delta (mtch_leql _ _ _ _ e).
    simpl.
    rewrite IHe.
    reflexivity.
Qed.

Definition subbot_string m n (Delta : string (S m) (S n)) M :=
  strsubst (mtch_Sm_Sn_inv _ _ Delta) Delta (botsub M).
Implicit Arguments subbot_string [m n].

Lemma Pi_subbot_srt : forall m n (Delta : string (S m) (S n)) s M,
  subbot (Pi Delta (srt s)) M = Pi (subbot_string Delta M) (srt s).
Proof.
intros.
exact (Pi_subst (S m) m (S n) n (mtch_Sm_Sn_inv _ _ Delta) Delta (srt s) (botsub M)).
Qed.

Lemma valid_concat' : forall m p n q (e : mtch m p n q) Gamma Delta rho Theta,
  Delta |= rho ; Gamma -> valid (Gamma @ Theta) -> valid Delta -> valid (Delta @ strsubst e Theta rho).
Proof.
induction e; simpl.
 trivial.
 intros Gamma Delta rho Theta.
   rewrite string_m_n with m n Theta (mtch_leql _ _ _ _ e).
   simpl.
   intros.
   elim (ctxt_strng _ (S n) (Gamma, head Theta (mtch_leql _ _ _ _ e)) (tail Theta (mtch_leql _ _ _ _ e))); auto.
   intros s H2.
   apply IHe with (Gamma, head Theta (mtch_leql m p (S n) (S q) e)).
    apply Weak_satisfy with s; assumption.
    assumption.
    split with s.
      apply Substitution with (sigma := rho) (A := srt (n:=n) s) (Delta := Gamma); assumption.
Qed.
     
Lemma satisfy_concat : forall m p n q (e : mtch m p n q) Gamma Delta rho Theta,
  Delta |= rho ; Gamma -> valid (Gamma @ Theta) -> valid Delta ->
  Delta @ strsubst e Theta rho |= subst_lift e rho ; Gamma @ Theta.
Proof.
 induction e; simpl.
  intros Gamma Delta rho Theta.
    rewrite string_n_n with m Theta.
    auto.
  intros Gamma Delta rho Theta.
    rewrite string_m_n with m n Theta (mtch_leql _ _ _ _ e).
    simpl.
    intros.
    apply IHe.
     simpl.
       elim (ctxt_strng m (S n) (Gamma, head Theta (mtch_leql _ _ _ _ e)) (tail Theta (mtch_leql _ _ _ _ e))); auto.
       intros s H2.
       apply Weak_satisfy with s; auto.
     assumption.
     elim (ctxt_strng m (S n) (Gamma, head Theta (mtch_leql _ _ _ _ e)) (tail Theta (mtch_leql _ _ _ _ e))); auto.
       intros s H2.
       split with s.
       apply Substitution with (A := srt (n:=n) s) (sigma := rho) (Delta := Gamma); assumption.
Qed.
    
Lemma conv_Pi_srt : forall m p (Delta : string m p) n (Theta : string n p) s s',
  Pi Delta (srt s) ~= Pi Theta (srt s') -> m = n.
Proof.
 induction Delta; simpl.
  intros.
    case (lt_eq_lt_dec n m).
    destruct 1.
     elim lt_not_le with n m.
      assumption.
      apply string_leq.
        assumption.
     auto.
     intro.
       rewrite string_m_n with n m Theta l in H.
       elim not_conv_pi_srt with m (head Theta l) (Pi (tail Theta l) (srt s')) s.
       apply conv_sym.
       assumption.
  intro n0.
    case (lt_eq_lt_dec n0 n).
    destruct 1.
     intro Theta.
       elim lt_not_le with n0 n.
        assumption.
        apply string_leq.
          assumption.
    rewrite e.
      clear n0 e.
      intro Theta.
      rewrite string_n_n with n Theta.
      clear Theta.
      intros.
      elim not_conv_pi_srt with n t (Pi Delta (srt s)) s'.
      assumption.
    intros.
      rewrite string_m_n with n0 n Theta l in H.
      simpl in H.
      apply IHDelta with (tail Theta l) s s'.
      apply conv_pi_injr with t (head Theta l).
      assumption.
Qed.

Lemma conv_Pi_srt' : forall m p (Delta : string m p) n (Theta : string n p) s s',
  Pi Delta (srt s) ~= Pi Theta (srt s') -> s = s'.
Proof.
 induction Delta.
  intro n.
    case (lt_eq_lt_dec m n).
    destruct 1.
     intro Theta.
       rewrite string_m_n with n m Theta l.
       intros.
       elim not_conv_pi_srt with m (head Theta l) (Pi (tail Theta l) (srt s')) s.
       apply conv_sym.
       assumption.
     rewrite e.
       intro Theta.
       rewrite string_n_n with n Theta.
       exact (conv_srt_inj n).
     intros H Theta.
       elim lt_not_le with n m.
       assumption.
       apply string_leq.
       assumption.
  intro p.
    case (lt_eq_lt_dec p n).
    destruct 1.
     intro Theta.
       elim lt_not_le with p n.
        assumption.
        apply string_leq.
	  assumption.
     rewrite e.
       intro Theta.
       rewrite string_n_n with n Theta.
       intros.
       elim not_conv_pi_srt with n t (Pi Delta (srt s)) s'.
       assumption.
     intros H Theta.
       rewrite string_m_n with p n Theta H.
       intros.
       apply IHDelta with p (tail Theta H).
       apply conv_pi_injr with t (head Theta H).
       assumption.
Qed.