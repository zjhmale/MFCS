Require Import Coq.Bool.Bool.

Check bool.
Check true.

Definition negb (b : bool) : bool :=
  match b with
    | false => true
    | true => false
  end.

Eval compute in (negb true).

Definition andb (b c : bool) : bool :=
  match b with
    | false => false
    | true => c
  end.

Eval compute in (andb true false).
Eval compute in (true && false).

Definition orb (b c : bool) : bool :=
  match b with
    | false => c
    | true => true
  end.

Eval compute in (orb true false).

Theorem negb_involutive : forall b : bool, negb (negb b) = b.

Proof.
  intros.
  case b.
  unfold negb.
  reflexivity.
  unfold negb.
  reflexivity.
Qed.

Theorem andb_comm : forall a b : bool, a && b = b && a.

Proof.
  intros.
  case a.
  simpl.
  case b.
  reflexivity.
  reflexivity.
  case b.
  reflexivity.
  reflexivity.
Qed.

Check (exists (n : nat),  n = 3).

Theorem true_or_false : forall b : bool, b = true \/ b = false.

Proof.
  intros.
  case b.
  left.
  reflexivity.
  right.
  reflexivity.
Qed.

Theorem use_rewrite : forall b : bool, b = true -> negb b = false.

Proof.
  intros bH tbH.
  rewrite tbH.
  unfold negb.
  reflexivity.
Qed.

Definition IsTrue (b : bool) : Prop :=
  match b with
    | true => True
    | false => False
  end.

Theorem diff_true_false : (true = false) -> False.

Proof.
  intro tfH.
  fold (IsTrue false).
  rewrite <- tfH.
  simpl.
  split.
Qed.

Goal true <> false.
intro tfH.
discriminate tfH.               (* small trick *)
Qed.

Lemma andb_compl : forall a b : bool, a = true /\ b = true -> a && b = true.
  intros.
  destruct H as [Ha Hb].
  rewrite Ha.
  simpl.
  rewrite Hb.
  reflexivity.
Qed.

Theorem andb_sound : forall a b : bool, a && b = true -> a = true /\ b = true.
  intros a b.
  case a.
  intro bH.
  split.
  reflexivity.
  exact bH.
  intro bH.
  discriminate bH.
Qed.

Theorem andb_ok : forall a b : bool, a = true /\ b = true <-> a && b = true.
  split.
  apply andb_compl.
  apply andb_sound.
Qed.

Lemma ex1 : exists b : bool, b && negb b = b.
  exists false.
  simpl.
  reflexivity.
Qed.

Theorem ex2 : forall a : bool, (exists b : bool, b && a = true) -> a = true.
  intros a H.
  elim H.
  intros b.
  case b.
  intro aH.
  exact aH.
  intro aH.
  discriminate aH.
Qed.

Definition allb (p : bool -> bool) : bool := p true && p false.

Theorem allb_compl : forall (p : bool -> bool), (forall b : bool, p b = true) -> (allb p = true).
  intros p H.
  unfold allb.
  apply andb_compl.
  split.
  apply H.
  apply H.
Qed.

Theorem allb_sound : forall (p : bool -> bool), (allb p = true) -> (forall b : bool, p b = true).
  intros p H b.
  cut (p true = true /\ p false = true).
  intro H'.
  destruct H' as [H1 H2].
  case b.
  exact H1.
  exact H2.
  apply andb_sound.
  exact H.
Qed.

Theorem allb_ok : forall (p : bool -> bool), (forall b : bool, p b = true) <-> (allb p = true).
  split.
  apply allb_compl.
  apply allb_sound.
Qed.

Section general.

Variable D : Set.
Variables P Q : D -> Prop.

Theorem AndAll : (forall x : D, P x) /\ (forall y : D, Q y) <-> forall z : D, P z /\ Q z.
  split.
  intros H d.
  destruct H as [HP HQ].
  split.
  apply HP.
  apply HQ.
  intro H.
  split.
  intro d.
  cut (P d /\ Q d).
  intro pqdH.
  destruct pqdH as [HP HQ].
  exact HP.
  apply H.
  intro d.
  cut (P d /\ Q d).
  intro pqdH.
  destruct pqdH as [HP HQ].
  exact HQ.
  apply H.
Qed.
  
End general.

Section deMorgan.

  Variable D : Set.
  Variables P Q : D -> Prop.
  Variable R : Prop.

  Theorem dm1 : (forall x : D, ~ P x) -> ~ (exists x : D, P x).
    intros Ha He.
    unfold not in Ha.
    destruct He as [d pd].
    eapply Ha.
    apply pd.
  Qed.

  Theorem dm2 : ~ (exists x : D, P x) -> forall x : D, ~ P x. (* also say ~ (P x) *)
    intros He d Hp.
    apply He.
    exists d.
    exact Hp.
  Qed.

  Theorem dm3 : (exists x : D, ~ P x) -> ~ forall x : D, P x.
    intros He Ha.
    destruct He as [d pd].
    apply pd.
    apply Ha.
  Qed.

  Require Import Classical.
  
  Theorem dm4 : ~ (forall x : D, P x) -> exists x : D, ~ (P x).
    intro Ha.
    apply NNPP.
    intro He.
    apply Ha.
    intro d.
    apply NNPP.
    intro npd.
    apply He.
    exists d.
    exact npd.
  Qed.
  
End deMorgan.

Section drinker.

  Require Import Classical.
  Variables Pubs People : Set.
  Variables InPub : People -> Pubs -> Prop.
  Variables Drinks : People -> Prop.

  (* In every non-empty pub there is sombeody, if he (or she) drinks then everybody drinks. *)
  Lemma drink : forall p : Pubs, (exists a : People, InPub a p) -> exists b : People, InPub b p /\ (Drinks b -> forall c : People, InPub c p -> Drinks c).
  Abort All.
End drinker.

Section cheat.
  
  Variable D : Set.
  Variables PP QQ: D -> Prop.
  Variable R : Prop.

  Lemma allMon : (forall x : D, PP x) -> (forall y : D, PP y -> QQ y) -> forall z : D, QQ z.
    auto.
  Qed.

  Theorem exOr : (exists x : D, PP x) \/ (exists y : D, QQ y) <-> exists z : D, PP z \/ QQ z.
    firstorder.
  Qed.

  Print exOr.                     (* a little complicated to prove this by hand *)
  
End cheat.