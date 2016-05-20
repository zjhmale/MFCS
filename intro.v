(* Basic Propositions *)

Variables P Q R : Prop.

(* simple tautology proof *)

Theorem I : P -> P.

Proof.
  intro H.                      (* to prove P -> Q, assume P and prove Q *)
  exact H.                      (* current goal is just the assumption *)
Qed.

Definition I2 : P -> P := fun H : P => H. (* Curry-Howard *)

Theorem K : P -> (Q -> P).

Proof.
  intro H1.
  intro H2.
  exact H1.
Qed.

Theorem S : (P -> Q -> R) -> (P -> Q) -> P -> R.

Proof.
  intro pqrH.
  intro pqH.
  intro pH.
  apply pqrH.                   (* MP *)
  exact pH.
  apply pqH.                    (* MP *)
  exact pH.
Qed.