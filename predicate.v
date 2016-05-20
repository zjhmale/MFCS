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
