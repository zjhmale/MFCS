(* Assume some basic Propositions *)

Variables P Q R : Prop.

(* conjunction *)

Theorem andCom : P /\ Q -> Q /\ P.

Proof.
  intro pqH.
  elim pqH.
  intros pH qH.
  split.
  exact qH.
  exact pH.
Qed.

Theorem curry : (P /\ Q -> R) -> (P -> Q -> R).

Proof.
  intros iH pH qH.
  apply iH.
  split.
  exact pH.
  exact qH.
Qed.

Theorem uncurry : (P -> Q -> R) -> (P /\ Q -> R).

Proof.
  intros pqrH pqH.
  apply pqrH.
  elim pqH.
  intros pH qH.
  exact pH.
  elim pqH.
  intros pH qH.
  exact qH.
Qed.

Theorem equiv : (P /\ Q -> R) <-> (P -> Q -> R).

Proof.
  split.
  exact curry.
  exact uncurry.
Qed.

Theorem orCom : P \/ Q -> Q \/ P.
  intro pqH.
  case pqH.
  intro pH.
  right.
  exact pH.
  intro qH.
  left.
  exact qH.
Qed.

Theorem triv : True.

Proof.
  split.                        (* to prove true, just need to prove nothing *)
Qed.

Theorem exFalso : False -> P.

Proof.
  intro fH.
  case fH.                      (* if get a contradiction, just can prove anything *)
Qed.

Theorem contra : ~ (P /\ ~ P).   (* ~ p desuger/unfold to p -> False *)

Proof.
  unfold not.
  intro pnpH.
  elim pnpH.
  intros pH npH.
  apply npH.
  exact pH.
Qed.