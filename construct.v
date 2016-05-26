(* natural deduction *)

Variables P Q R : Prop.

Theorem impliIntro : P -> Q -> (P -> Q).
  intros p q.
  intro H.
  exact q.
Qed.

Theorem impliElim : P -> (P -> Q) -> Q.
  intros p pq.
  apply pq.
  exact p.
Qed.

Theorem conjIntro : P -> Q -> (P /\ Q).
  intros p q.
  split.
  exact p.
  exact q.
Qed.

Theorem conjElimL : (P /\ Q) -> P.
  intro.
  elim H.
  intros p q.
  exact p.
Qed.

Theorem conjElimL2 : (P /\ Q) -> P.
  intro.
  destruct H as [p q].
  exact p.
Qed.

Theorem conjElimR : (P /\ Q) -> Q.
  intro.
  elim H.
  intros p q.
  exact q.
Qed.

Theorem conjElimR2 : (P /\ Q) -> Q.
  intro.
  destruct H as [p q].
  exact q.
Qed.

Theorem disjIntroL : P -> (P \/ Q).
  left.
  exact H.
Qed.

Theorem disjIntroR : Q -> (P \/ Q).
  right.
  exact H.
Qed.

Theorem disjElim : (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
  intro H.
  intros pr qr.
  case H.
  exact pr.
  exact qr.
Qed.

(* more natural deduction *)

Variables A B C : Prop.

Theorem ex1 : (A /\ B) /\ C -> A.
  intro H.
  destruct H as [ab c].
  elim ab.
  intros a b.
  exact a.
Qed.

Theorem ex2 : (A /\ B) /\ C -> (B /\ C).
  intro H.
  elim H.
  intros ab c.
  destruct ab as [a b].
  split.
  exact b.
  exact c.
Qed.

Theorem ex3 : (A /\ B) /\ C -> A /\ (B /\ C).
  intro H.
  destruct H as [ab c].
  destruct ab as [a b].
  split.
  exact a.
  split.
  exact b.
  exact c.
Qed.