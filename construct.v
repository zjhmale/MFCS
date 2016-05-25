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